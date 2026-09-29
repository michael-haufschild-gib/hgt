import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw
import GaloisForLFunctions.RHTower.MobiusCubicSourceCriticalFloor
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel

/-!
# Weighted line energies of finite Möbius sections

For a weight `w` on the vertical line `Re s = σ`, the weighted line energy of the finite Möbius
section is

```text
E_N(w, σ) = ∫ |Σ_{n≤N} μ(n) n^{-σ-iτ}|² w(τ) dτ .
```

Suppose `w` dominates a positive multiple of `|Γ(σ+iτ)|²` and has a finite second moment
`∫ (1+τ²) w(τ) dτ < ∞`. Then, off the line `σ = Θ` (with `Θ = sup Re ρ` the zero abscissa), the
energies are bounded in `N` exactly when `Θ < σ`. Every positive weighted `L²` energy of Möbius
prefixes on a vertical line thus has the zero abscissa as its threshold.

Mechanism.
* Lower comparison: domination and Plancherel bound the energy below by the Gamma–Hankel energy at
  exponent `2σ`, whose divergence threshold is `2Θ`.
* Upper comparison: on `Re s = σ > Θ`, Abel summation against Littlewood's Mertens bound
  `M(x) = O(x^{Θ+ε})` gives `|Σ_{n≤N} μ(n) n^{-s}| ≤ K (1+|τ|)` uniformly in `N`. The second moment
  of `w` absorbs this linear growth.
-/

noncomputable section

open MeasureTheory Finset Complex

namespace RHTower

/-- Weighted energy of the finite Möbius section `Σ_{n≤N} μ(n) n^{-s}` on the vertical line
`Re s = σ`. -/
def mobiusWeightedLineEnergy (w : ℝ → ℝ) (σ : ℝ) (N : ℕ) : ℝ :=
  ∫ τ : ℝ, ‖edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 * w τ

/-- A finite Möbius section, reindexed over `range N`. -/
theorem edPoly_mobCoeff_Icc_eq_sum_range (N : ℕ) (s : ℂ) :
    edPoly mobCoeff (Icc 1 N) s =
      ∑ i ∈ range N, (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) • mobCoeff (i + 1) := by
  rw [edPoly, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show N + 1 - 1 = N by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, show 1 + i = i + 1 by omega]
  push_cast
  ring

/-- The shifted Möbius partial sums are the Mertens partial sums. -/
theorem sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum (k : ℕ) :
    ∑ i ∈ range k, mobCoeff (i + 1) = mobiusMertensPartialSum k := by
  rw [mobiusMertensPartialSum, Finset.sum_range_succ']
  simp [mobiusComplexCoefficient, mobCoeff]

/-- **Uniform Abel bound right of the zero abscissa.** On `Re s = σ > Θ` the finite Möbius
sections grow at most linearly in the height, uniformly in the cutoff: Abel summation moves the
coefficients onto the Mertens sums `M(k) = O(k^a)`, `Θ < a < σ`, and the unit differences of
`k^{-s}` are `O(|s| k^{-σ-1})`. -/
theorem exists_norm_edPoly_mobCoeff_line_le_of_zetaZeroAbscissa_lt {σ : ℝ}
    (hσ : zetaZeroAbscissa < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (τ : ℝ),
      ‖edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ K * (1 + |τ|) := by
  set a : ℝ := (zetaZeroAbscissa + σ) / 2 with ha
  have hhalf := half_le_zetaZeroAbscissa
  have haσ : a < σ := by rw [ha]; linarith
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hσ0 : 0 < σ := by linarith
  obtain ⟨C, hC0, hC⟩ :=
    mobiusMertens_subpower_zetaZeroAbscissa (a - zetaZeroAbscissa) (by rw [ha]; linarith)
  set D : ℝ := C * (2 : ℝ) ^ a with hD
  have hD0 : 0 ≤ D := by positivity
  have hA : ∀ k : ℕ, 1 ≤ k → ‖∑ i ∈ range k, mobCoeff (i + 1)‖ ≤ D * (k : ℝ) ^ a := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum]
    have h := hC k
    rw [show zetaZeroAbscissa + (a - zetaZeroAbscissa) = a by ring] at h
    refine h.trans ?_
    rw [hD, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) ha0
  have hsum : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (a - σ - 1)) := by
    refine ((Real.summable_one_div_nat_add_rpow 1 (1 + σ - a)).mpr (by linarith)).congr
      fun i => ?_
    have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [abs_of_pos hpos, one_div, ← Real.rpow_neg hpos.le]
    ring_nf
  set S : ℝ := ∑' i : ℕ, ((i : ℝ) + 1) ^ (a - σ - 1) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun i => by positivity
  refine ⟨D * (1 + σ * S + S), by positivity, fun N τ => ?_⟩
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsnorm : ‖s‖ ≤ σ + |τ| := by
    calc ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = σ + |τ| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hσ0]
  have hfinal : D + D * (σ + |τ|) * S ≤ D * (1 + σ * S + S) * (1 + |τ|) := by
    have h1 : 0 ≤ D * |τ| := mul_nonneg hD0 (abs_nonneg τ)
    have h2 : 0 ≤ D * σ * S * |τ| := by positivity
    have h3 : 0 ≤ D * S := mul_nonneg hD0 hS0
    nlinarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.Icc_eq_empty_of_lt one_pos, edPoly, Finset.sum_empty, norm_zero]
    positivity
  set b : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hb
  set g : ℕ → ℂ := fun i => mobCoeff (i + 1) with hg
  have hnormb : ∀ i : ℕ, ‖b i‖ = ((i : ℝ) + 1) ^ (-σ) := by
    intro i
    rw [hb, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, hsre]
  have hdiff : ∀ i : ℕ, ‖b (i + 1) - b i‖ ≤ ‖s‖ * ((i : ℝ) + 1) ^ (-σ - 1) := by
    intro i
    have hstep := GaloisForLFunctions.RHTower.norm_cpow_unit_diff_le (w := s)
      (by rw [hsre]; exact hσ0) (x := (i : ℝ) + 1) (by positivity)
    rw [hsre] at hstep
    have hcast : ((((i + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) = ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [norm_sub_rev, hb]
    simp only
    rw [hcast]
    exact hstep
  have hby := Finset.sum_range_by_parts b g N
  rw [edPoly_mobCoeff_Icc_eq_sum_range]
  change ‖∑ i ∈ range N, b i • g i‖ ≤ _
  rw [hby]
  have hhead : ‖b (N - 1) • ∑ i ∈ range N, g i‖ ≤ D := by
    rw [norm_smul, hnormb]
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      rw [Nat.cast_sub hN]; push_cast; ring
    rw [hcast]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hAN := hA N hN
    calc (N : ℝ) ^ (-σ) * ‖∑ i ∈ range N, g i‖
        ≤ (N : ℝ) ^ (-σ) * (D * (N : ℝ) ^ a) :=
          mul_le_mul_of_nonneg_left hAN (by positivity)
      _ = D * (N : ℝ) ^ (a - σ) := by
          rw [Real.rpow_sub (by linarith), Real.rpow_neg (by linarith)]
          field_simp
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)) hD0
      _ = D := mul_one D
  have hterm : ∀ i : ℕ, ‖(b (i + 1) - b i) • ∑ j ∈ range (i + 1), g j‖
      ≤ D * ‖s‖ * ((i : ℝ) + 1) ^ (a - σ - 1) := by
    intro i
    have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hAi := hA (i + 1) (by omega)
    push_cast at hAi
    rw [norm_smul]
    calc ‖b (i + 1) - b i‖ * ‖∑ j ∈ range (i + 1), g j‖
        ≤ (‖s‖ * ((i : ℝ) + 1) ^ (-σ - 1)) * (D * ((i : ℝ) + 1) ^ a) :=
          mul_le_mul (hdiff i) hAi (norm_nonneg _) (by positivity)
      _ = D * ‖s‖ * ((i : ℝ) + 1) ^ (a - σ - 1) := by
          rw [show a - σ - 1 = (-σ - 1) + a by ring, Real.rpow_add hpos]
          ring
  calc ‖b (N - 1) • ∑ i ∈ range N, g i
        - ∑ i ∈ range (N - 1), (b (i + 1) - b i) • ∑ j ∈ range (i + 1), g j‖
      ≤ ‖b (N - 1) • ∑ i ∈ range N, g i‖
        + ‖∑ i ∈ range (N - 1), (b (i + 1) - b i) • ∑ j ∈ range (i + 1), g j‖ :=
        norm_sub_le _ _
    _ ≤ D + ∑ i ∈ range (N - 1), D * ‖s‖ * ((i : ℝ) + 1) ^ (a - σ - 1) :=
        add_le_add hhead ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i))
    _ = D + D * ‖s‖ * ∑ i ∈ range (N - 1), ((i : ℝ) + 1) ^ (a - σ - 1) := by
        rw [Finset.mul_sum]
    _ ≤ D + D * ‖s‖ * S := by
        gcongr
        exact hsum.sum_le_tsum _ fun i _ => by positivity
    _ ≤ D + D * (σ + |τ|) * S := by gcongr
    _ ≤ D * (1 + σ * S + S) * (1 + |τ|) := hfinal

/-- **Upper comparison.** Right of the zero abscissa, every weight with a finite second moment has
uniformly bounded Möbius line energies. -/
theorem exists_forall_mobiusWeightedLineEnergy_le_of_zetaZeroAbscissa_lt {w : ℝ → ℝ} {σ : ℝ}
    (hσ : zetaZeroAbscissa < σ) (hw0 : ∀ τ, 0 ≤ w τ)
    (hmom : Integrable (fun τ : ℝ => (1 + τ ^ 2) * w τ)) :
    ∃ B : ℝ, ∀ N : ℕ, mobiusWeightedLineEnergy w σ N ≤ B := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_edPoly_mobCoeff_line_le_of_zetaZeroAbscissa_lt hσ
  refine ⟨∫ τ : ℝ, 2 * K ^ 2 * ((1 + τ ^ 2) * w τ), fun N => ?_⟩
  refine integral_mono_of_nonneg (ae_of_all _ fun τ => mul_nonneg (sq_nonneg _) (hw0 τ))
    (hmom.const_mul (2 * K ^ 2)) (ae_of_all _ fun τ => ?_)
  have hP := hK N τ
  have hsq : ‖edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ 2 * K ^ 2 * (1 + τ ^ 2) := by
    have h1 : ‖edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ (K * (1 + |τ|)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hP 2
    have h2 : (1 + |τ|) ^ 2 ≤ 2 * (1 + τ ^ 2) := by
      nlinarith [sq_abs τ, sq_nonneg (1 - |τ|)]
    calc _ ≤ (K * (1 + |τ|)) ^ 2 := h1
      _ = K ^ 2 * (1 + |τ|) ^ 2 := by ring
      _ ≤ K ^ 2 * (2 * (1 + τ ^ 2)) := mul_le_mul_of_nonneg_left h2 (sq_nonneg K)
      _ = 2 * K ^ 2 * (1 + τ ^ 2) := by ring
  calc ‖edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 * w τ
      ≤ 2 * K ^ 2 * (1 + τ ^ 2) * w τ := mul_le_mul_of_nonneg_right hsq (hw0 τ)
    _ = 2 * K ^ 2 * ((1 + τ ^ 2) * w τ) := by ring

/-- **Lower comparison.** A weight dominating `c |Γ(σ+iτ)|²` controls the Gamma–Hankel energy at
exponent `2σ`: `E_N(2σ) ≤ E_N(w, σ) / (2πc)`. -/
theorem finiteMobiusGammaHankelEnergy_le_mobiusWeightedLineEnergy {w : ℝ → ℝ} {σ c : ℝ}
    (hσ0 : 0 < σ) (hw : Measurable w) (hc : 0 < c)
    (hlow : ∀ τ : ℝ, c * ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ w τ)
    (hmom : Integrable (fun τ : ℝ => (1 + τ ^ 2) * w τ)) (N : ℕ) :
    finiteMobiusGammaHankelEnergy N (2 * σ) ≤
      mobiusWeightedLineEnergy w σ N / (2 * Real.pi * c) := by
  have hw0 : ∀ τ, 0 ≤ w τ := fun τ => le_trans (by positivity) (hlow τ)
  have hwint : Integrable w := by
    refine hmom.mono' hw.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 τ)]
    nlinarith [sq_nonneg τ, hw0 τ]
  set P : ℝ → ℂ := fun τ => edPoly mobCoeff (Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I) with hPdef
  have hPcont : Continuous P := by
    have hd := differentiable_edPoly mobCoeff (s := Icc 1 N)
      (fun n hn => (Finset.mem_Icc.mp hn).1)
    exact hd.continuous.comp (by fun_prop)
  have hPbound : ∀ τ : ℝ, ‖P τ‖ ≤ N := fun τ =>
    norm_edPoly_mobCoeff_le N (by simp [hσ0.le])
  have hint : Integrable (fun τ : ℝ => ‖P τ‖ ^ 2 * w τ) := by
    refine (hwint.const_mul ((N : ℝ) ^ 2)).mono'
      ((hPcont.norm.pow 2).aestronglyMeasurable.mul hw.aestronglyMeasurable)
      (ae_of_all _ fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hw0 τ))]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hPbound τ) 2) (hw0 τ)
  have hplanch : (∫ u : ℝ, ‖Complex.Gamma ((σ : ℂ) + (u : ℂ) * I) * P u‖ ^ 2) =
      2 * Real.pi * finiteMobiusGammaHankelEnergy N (2 * σ) :=
    CubicGamma.integral_norm_sq_gamma_mul_edPoly_mobCoeff_line_sigma N hσ0
  have hmono : (∫ u : ℝ, ‖Complex.Gamma ((σ : ℂ) + (u : ℂ) * I) * P u‖ ^ 2) ≤
      ∫ u : ℝ, ‖P u‖ ^ 2 * w u / c := by
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (hint.div_const c)
      (ae_of_all _ fun u => ?_)
    dsimp only
    rw [norm_mul, mul_pow, le_div_iff₀ hc]
    have := mul_le_mul_of_nonneg_left (hlow u) (sq_nonneg ‖P u‖)
    nlinarith
  rw [integral_div] at hmono
  rw [hplanch] at hmono
  rw [le_div_iff₀ (by positivity)]
  have hpi : 0 < Real.pi := Real.pi_pos
  have key : 2 * Real.pi * finiteMobiusGammaHankelEnergy N (2 * σ) * c ≤
      ∫ u : ℝ, ‖P u‖ ^ 2 * w u := by
    rwa [le_div_iff₀ hc] at hmono
  calc finiteMobiusGammaHankelEnergy N (2 * σ) * (2 * Real.pi * c)
      = 2 * Real.pi * finiteMobiusGammaHankelEnergy N (2 * σ) * c := by ring
    _ ≤ ∫ u : ℝ, ‖P u‖ ^ 2 * w u := key
    _ = mobiusWeightedLineEnergy w σ N := rfl

/-- **Weighted line-energy threshold.** Let `w` dominate `c |Γ(σ+iτ)|²` with `c > 0` and have a
finite second moment. Off `σ = Θ`, the weighted Möbius line energies
`∫ |Σ_{n≤N} μ(n) n^{-σ-iτ}|² w(τ) dτ` are bounded in `N` exactly when `Θ < σ`. No weight of this
class yields a Möbius-cancellation carrier whose threshold differs from the zero abscissa. -/
theorem bddAbove_range_mobiusWeightedLineEnergy_iff {w : ℝ → ℝ} {σ c : ℝ}
    (hσ0 : 0 < σ) (hσΘ : σ ≠ zetaZeroAbscissa) (hw : Measurable w) (hc : 0 < c)
    (hlow : ∀ τ : ℝ, c * ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ w τ)
    (hmom : Integrable (fun τ : ℝ => (1 + τ ^ 2) * w τ)) :
    BddAbove (Set.range (mobiusWeightedLineEnergy w σ)) ↔ zetaZeroAbscissa < σ := by
  constructor
  · rintro ⟨B, hB⟩
    have hbdd : BddAbove (Set.range fun N : ℕ => finiteMobiusGammaHankelEnergy N (2 * σ)) := by
      refine ⟨B / (2 * Real.pi * c), ?_⟩
      rintro _ ⟨N, rfl⟩
      refine (finiteMobiusGammaHankelEnergy_le_mobiusWeightedLineEnergy hσ0 hw hc hlow hmom
        N).trans ?_
      exact div_le_div_of_nonneg_right (hB ⟨N, rfl⟩) (by positivity)
    have h := (bddAbove_range_finiteMobiusGammaHankelEnergy_iff (by positivity)
      (fun h => hσΘ (by linarith))).mp hbdd
    linarith
  · intro hσ
    obtain ⟨B, hB⟩ := exists_forall_mobiusWeightedLineEnergy_le_of_zetaZeroAbscissa_lt hσ
      (fun τ => le_trans (by positivity) (hlow τ)) hmom
    exact ⟨B, by rintro _ ⟨N, rfl⟩; exact hB N⟩

end RHTower
