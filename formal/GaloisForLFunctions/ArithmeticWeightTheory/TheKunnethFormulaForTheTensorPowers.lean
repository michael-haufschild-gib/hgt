import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesSampleEveryTopLayer
import GaloisForLFunctions.SurfaceOfSpecZ.TheTraceZetaFunctionAtThePowerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovCountAtThePrimePowerDegrees

/-!
# The Künneth formula for the tensor powers

Over a curve the trace formula writes `L(F^{⊗m})` through the cohomology of `F^{⊗m}`, and Künneth
splits it into constituents; only the geometrically trivial ones carry poles. For the virtual
motive `M = Σ_z e_z ℤ(−z)` of a configuration the analogous decomposition is explicit.

**Theorem** (`tensorSeries_eq_tsum`). Let `Z` be a tempered configuration whose exponents have real
part `≤ b` (`TopDepth Z b`), `e_z` the spline coefficients, `m ≥ 0` and `Re s > 1 + m b`. Then

  `Σ_n Λ(n) (2 Re S(log n))^m n^{−s} = Σ_{z₁,…,z_m} e_{z₁}⋯e_{z_m} · (−ζ′/ζ)(s − z₁ − ⋯ − z_m)`,

the sum on the right absolutely convergent over all `m`-tuples of exponents.

So every constituent of `M^{⊗m}` is the Tate twist `ℤ(−z₁ − ⋯ − z_m)`: its log-derivative is a
shifted `−ζ′/ζ`, with a pole at `s = 1 + z₁ + ⋯ + z_m`. No constituent is geometrically
nontrivial; the analogue of `H²_c` is the whole tensor power, and the top pole of the series sits
where the weights put it (`TheTensorPowersHaveExactlyTheirWeight`). This is the precise sense in
which `M` is geometrically constant.

**Proof.** Expand `(Σ_z e_z n^z)^m` over `m`-tuples (`hasSum_pow_tuple`, by induction through
`Fin.cons` and products of absolutely summable families), bound `|e_{z⃗} n^{Σz − s}|` by
`Λ(n) n^{mb − Re s} Π|e_{z_i}|`, and exchange the sums.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticOrientationGeometry SquareRootThreshold SurfaceOfSpecZ ArithmeticFunction

/-! ### Powers of absolutely convergent series -/

/-- **Powers of an absolutely convergent series are sums over tuples.** -/
theorem hasSum_pow_tuple {f : ℂ → ℂ} (hf : Summable fun z => ‖f z‖) :
    ∀ m : ℕ, Summable (fun w : Fin m → ℂ => ‖∏ i, f (w i)‖) ∧
      (∑' z, f z) ^ m = ∑' w : Fin m → ℂ, ∏ i, f (w i)
  | 0 => by
    refine ⟨Summable.of_finite, ?_⟩
    simp
  | m + 1 => by
    obtain ⟨ih1, ih2⟩ := hasSum_pow_tuple hf m
    set e := Fin.consEquiv (fun _ : Fin (m + 1) => ℂ)
    have hcons : ∀ p : ℂ × (Fin m → ℂ), ∏ i, f (e p i) = f p.1 * ∏ i, f (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [e, Fin.consEquiv]
    have hsum : Summable fun p : ℂ × (Fin m → ℂ) => ‖f p.1 * ∏ i, f (p.2 i)‖ := by
      refine (hf.mul_norm ih1).congr fun p => ?_
      rw [norm_mul]
    refine ⟨?_, ?_⟩
    · rw [← e.summable_iff]
      exact hsum.congr fun p => by simp only [Function.comp, hcons p]
    · rw [pow_succ', ih2, tsum_mul_tsum_of_summable_norm hf ih1, ← e.tsum_eq]
      exact tsum_congr fun p => (hcons p).symm

/-! ### The Künneth formula -/

/-- The `n = j + 1` term of `Σ_n Λ(n) (2 Re S_Z(log n))^m n^{−s}`. -/
def tensorSeriesTerm (Z : ZeroConfig) (m : ℕ) (s : ℂ) (j : ℕ) : ℂ :=
  (Λ (j + 1) : ℂ) * (((2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) ^ m : ℝ) : ℂ) *
    ((j : ℂ) + 1) ^ (-s)

/-- **The Künneth formula for the tensor powers of the zero motive.** -/
theorem tensorSeries_eq_tsum {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ} (htop : TopDepth Z b)
    (m : ℕ) {s : ℂ} (hs : 1 + m * b < s.re) :
    Summable (tensorSeriesTerm Z m s) ∧
      ∑' j, tensorSeriesTerm Z m s j =
        ∑' w : Fin m → ℂ, (∏ i, evenCoeff Z (boxSpline 1 3) (w i)) *
          (-logDeriv riemannZeta (s - ∑ i, w i)) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  obtain ⟨hP1, -⟩ := hasSum_pow_tuple hE m
  set σ := s.re with hσdef
  have hσ' : 1 < σ - m * b := by linarith
  -- a tuple with nonzero weight has total real part at most `m b`
  have hre : ∀ w : Fin m → ℂ, ∏ i, e (w i) ≠ 0 → (∑ i, w i).re ≤ m * b := by
    intro w hw
    rw [Complex.re_sum]
    calc ∑ i, (w i).re ≤ ∑ _i : Fin m, b :=
          Finset.sum_le_sum fun i _ => htop _ (Finset.prod_ne_zero_iff.mp hw i (Finset.mem_univ i))
      _ = m * b := by simp
  -- the double family
  set F : ℕ → (Fin m → ℂ) → ℂ := fun j w =>
    (Λ (j + 1) : ℂ) * ((∏ i, e (w i)) * ((j : ℂ) + 1) ^ (-(s - ∑ i, w i))) with hFdef
  have hFn : ∀ j w, ‖F j w‖ ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-(σ - m * b)) * ‖∏ i, e (w i)‖ := by
    intro j w
    by_cases hw : ∏ i, e (w i) = 0
    · simp [hFdef, hw]
    have h1 := hre w hw
    simp only [hFdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg, norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-(s - ∑ i, w i)).re ≤ ((j : ℝ) + 1) ^ (-(σ - m * b)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp only [Complex.neg_re, Complex.sub_re]
      linarith
    have hΛ0 := vonMangoldt_nonneg (n := j + 1)
    calc Λ (j + 1) * (‖∏ i, e (w i)‖ * ((j : ℝ) + 1) ^ (-(s - ∑ i, w i)).re)
        ≤ Λ (j + 1) * (‖∏ i, e (w i)‖ * ((j : ℝ) + 1) ^ (-(σ - m * b))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) hΛ0
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × (Fin m → ℂ) =>
      Λ (p.1 + 1) * ((p.1 : ℝ) + 1) ^ (-(σ - m * b)) * ‖∏ i, e (p.2 i)‖ :=
    (summable_vonMangoldt_rpow hσ').mul_of_nonneg hP1
      (fun j => mul_nonneg vonMangoldt_nonneg (by positivity)) (fun _ => norm_nonneg _)
  have hFsum : Summable (Function.uncurry F) :=
    Summable.of_norm_bounded hprod fun p => hFn p.1 p.2
  -- each prime-power term is the sum over tuples
  have hj : ∀ j : ℕ, tensorSeriesTerm Z m s j = ∑' w, F j w := by
    intro j
    set L : ℝ := Real.log (j + 1) with hLdef
    have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have htr := (two_re_lagStructure_eq Z hZ (contDiff_boxSpline (r := 1) one_pos 2)
      (boxSpline_support (r := 1) one_pos 3) L).2
    have hfj : Summable fun z => ‖e z * cexp (z * (L : ℂ))‖ := by
      refine (hE.mul_right (Real.exp (b * L))).of_nonneg_of_le (fun _ => norm_nonneg _) fun z => ?_
      by_cases hz : e z = 0
      · simp [hz]
      have h1 := htop z hz
      rw [norm_mul, Complex.norm_exp]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right h1 hL0
    obtain ⟨-, hpow⟩ := hasSum_pow_tuple hfj m
    have hterm : ∀ w : Fin m → ℂ, ∏ i, (e (w i) * cexp (w i * (L : ℂ))) =
        (∏ i, e (w i)) * cexp ((∑ i, w i) * (L : ℂ)) := by
      intro w
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_mul]
    have hcpow : ∀ w : Fin m → ℂ, cexp ((∑ i, w i) * (L : ℂ)) * ((j : ℂ) + 1) ^ (-s) =
        ((j : ℂ) + 1) ^ (-(s - ∑ i, w i)) := by
      intro w
      rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, ← Complex.exp_add]
      congr 1
      rw [hLdef]
      push_cast
      ring
    unfold tensorSeriesTerm
    rw [Complex.ofReal_pow, ← hLdef, htr, hpow, tsum_congr hterm, mul_assoc, ← tsum_mul_right,
      ← tsum_mul_left]
    refine tsum_congr fun w => ?_
    simp only [hFdef]
    rw [mul_assoc, hcpow w]
  have hw : ∀ w : Fin m → ℂ, ∑' j, F j w = (∏ i, e (w i)) * (-logDeriv riemannZeta (s - ∑ i, w i)) := by
    intro w
    by_cases hw0 : ∏ i, e (w i) = 0
    · simp [hFdef, hw0]
    have hres : 1 < (s - ∑ i, w i).re := by
      have := hre w hw0
      rw [Complex.sub_re]
      linarith
    obtain ⟨-, hsum⟩ := summable_tsum_vonMangoldt hres
    rw [← hsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hFdef]
    ring
  refine ⟨(hFsum.prod).congr fun j => (hj j).symm, ?_⟩
  rw [tsum_congr hj, hFsum.tsum_comm, tsum_congr hw]

end GaloisForLFunctions.ArithmeticWeightTheory
