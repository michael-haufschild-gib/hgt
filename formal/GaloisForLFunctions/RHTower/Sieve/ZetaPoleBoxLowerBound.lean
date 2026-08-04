import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# Zeta near its pole

`ZetaBoxLowerBound.lean` bounds `‖ζ‖` below on a box `[1, 1+η] × [ε, T]` that keeps away from the
pole; the argument is a compactness minimum and it breaks at `t = 0`, where `ζ` is unbounded.  The
frequencies of the Halász mechanism, however, run over a whole interval `|t| ≤ T`, and the segment
near zero cannot be discarded.

The repair is to minimise not `ζ` but the entire function `(s − 1)ζ(s)`, which the corpus already
owns as `zetaEntire`.  It is nonvanishing on `re s ≥ 1` — off the pole because `ζ` is, and at the
pole because its value there is the residue `1` — so on a compact box containing `s = 1` it has a
positive minimum `c`, and

    ‖ζ(σ+it)‖  =  ‖zetaEntire(σ+it)‖ / ‖σ+it−1‖  ≥  c/(η + T + 1)

for every `σ > 1` in the box.  The pole helps rather than hinders: `ζ` is *large* near `s = 1`.

Together with the strip bound this covers every real frequency.
-/

namespace RHTower.Sieve

open Complex

/-- The entire multiple of zeta does not vanish on the closed half-plane `re s ≥ 1`. -/
theorem zetaEntire_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : RHTower.zetaEntire s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · rw [h, RHTower.zetaEntire]
    simp only [sub_self, zero_mul, zero_add]
    exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  · rw [RHTower.zetaEntire_eq h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re hs)

/-- The distance to the pole across the box. -/
theorem norm_sub_one_le_box {η T₀ σ t : ℝ} (hη : 0 ≤ η) (hT₀ : 0 ≤ T₀)
    (hσ : σ ∈ Set.Icc (1 : ℝ) (1 + η)) (ht : t ∈ Set.Icc (-T₀) T₀) :
    ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ η + T₀ + 1 := by
  have hrw : ((σ : ℂ) + (t : ℂ) * Complex.I) - 1 = (((σ - 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hrw]
  refine le_trans (norm_add_le _ _) ?_
  rw [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  have h1 : |σ - 1| ≤ η := by
    rw [abs_of_nonneg (by linarith [hσ.1])]
    linarith [hσ.2]
  have h2 : |t| ≤ T₀ := abs_le.2 ⟨ht.1, ht.2⟩
  linarith

/-- **Quantitative nonvanishing of zeta on a box straddling the pole.** -/
theorem exists_pos_lower_bound_zeta_pole_box {η T₀ : ℝ} (hη : 0 ≤ η) (hT₀ : 0 ≤ T₀) :
    ∃ c > 0, ∀ σ ∈ Set.Ioc (1 : ℝ) (1 + η), ∀ t ∈ Set.Icc (-T₀) T₀,
      c ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set K : Set (ℝ × ℝ) := Set.Icc (1 : ℝ) (1 + η) ×ˢ Set.Icc (-T₀) T₀ with hK
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(1, 0), ⟨le_refl 1, by linarith⟩, ⟨by linarith, hT₀⟩⟩
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ => ‖RHTower.zetaEntire ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)‖) K := by
    refine Continuous.continuousOn ?_
    have h1 : Continuous (fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) := by fun_prop
    exact (RHTower.differentiable_zetaEntire.continuous.comp h1).norm
  obtain ⟨q₀, hq₀, hmin⟩ := hcompact.exists_isMinOn hne hcont
  have hre : ((q₀.1 : ℂ) + (q₀.2 : ℂ) * Complex.I).re = q₀.1 := by simp
  have hc0 : 0 < ‖RHTower.zetaEntire ((q₀.1 : ℂ) + (q₀.2 : ℂ) * Complex.I)‖ := by
    refine norm_pos_iff.2 (zetaEntire_ne_zero_of_one_le_re ?_)
    rw [hre]
    exact hq₀.1.1
  refine ⟨‖RHTower.zetaEntire ((q₀.1 : ℂ) + (q₀.2 : ℂ) * Complex.I)‖ / (η + T₀ + 1),
    by positivity, ?_⟩
  intro σ hσ t ht
  have hσI : σ ∈ Set.Icc (1 : ℝ) (1 + η) := ⟨le_of_lt hσ.1, hσ.2⟩
  have hmem : (σ, t) ∈ K := ⟨hσI, ht⟩
  have hlow := hmin hmem
  have hs1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    have hreq : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [hcon] at hreq
    simp only [Complex.one_re] at hreq
    linarith [hσ.1]
  have hfac : RHTower.zetaEntire ((σ : ℂ) + (t : ℂ) * Complex.I)
      = (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) * riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    RHTower.zetaEntire_eq hs1
  have hnorm : ‖RHTower.zetaEntire ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
        * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [hfac, norm_mul]
  have hdist := norm_sub_one_le_box hη hT₀ hσI ht
  have hzn : 0 ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  have hden : (0 : ℝ) < η + T₀ + 1 := by linarith
  rw [div_le_iff₀ hden]
  calc ‖RHTower.zetaEntire ((q₀.1 : ℂ) + (q₀.2 : ℂ) * Complex.I)‖
      ≤ ‖RHTower.zetaEntire ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hlow
    _ = ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
        * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hnorm
    _ ≤ (η + T₀ + 1) * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hdist hzn
    _ = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (η + T₀ + 1) := by ring

/-- **The prime sum on a box straddling the pole.** -/
theorem exists_le_tsum_re_prime_cpow_pole_box {η T₀ : ℝ} (hη : 0 ≤ η) (hT₀ : 0 ≤ T₀) :
    ∃ L : ℝ, ∀ σ ∈ Set.Ioc (1 : ℝ) (1 + η), ∀ t ∈ Set.Icc (-T₀) T₀,
      L ≤ ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_lower_bound_zeta_pole_box hη hT₀
  refine ⟨Real.log c - Real.pi ^ 2 / 6, ?_⟩
  intro σ hσ t ht
  exact le_tsum_re_prime_cpow_of_log_le hσ.1 (Real.log_le_log hc (hbound σ hσ t ht))

/-- **The cosine sum at a bounded frequency.**  An absolute constant, valid at every `|t| ≤ 9`,
including `t = 0` and the whole neighbourhood of the pole. -/
theorem exists_sum_cos_div_prime_ge_small :
    ∃ C : ℝ, ∀ z : ℕ, 3 ≤ z → ∀ t : ℝ, |t| ≤ 9 →
      -C ≤ ∑ p ∈ Nat.primesLE z, Real.cos (t * Real.log p) / (p : ℝ) := by
  obtain ⟨L, hL⟩ := exists_le_tsum_re_prime_cpow_pole_box (η := 1) (T₀ := 9)
    (by norm_num) (by norm_num)
  refine ⟨-(L - 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2
    - (1 + Real.log 4)), ?_⟩
  intro z hz t ht
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hmem : 1 + 1 / Real.log (z : ℝ) ∈ Set.Ioc (1 : ℝ) (1 + 1) := by
    constructor
    · have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
      linarith
    · have : 1 / Real.log (z : ℝ) ≤ 1 := by
        rw [div_le_one hlogz0]
        exact hlogz
      linarith
  have htmem : t ∈ Set.Icc (-9 : ℝ) 9 := abs_le.1 ht
  have hbase := sum_cos_div_prime_ge_of_le hz (hL _ hmem t htmem)
  linarith

end RHTower.Sieve
