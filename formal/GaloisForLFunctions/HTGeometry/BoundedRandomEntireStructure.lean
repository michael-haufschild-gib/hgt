import GaloisForLFunctions.HTGeometry.BoundedRandomEntireSeries

/-!
# Continuity and the head–tail decomposition of the bounded random entire series

The clamped coefficients are bounded by `1/n!` uniformly in the ambient sequence, so the series
converges locally uniformly in the pair `(sequence, point)`.  The resulting source therefore depends
continuously — hence measurably — on the ambient sequence, and splits at every index into its
polynomial head and a tail determined by the shifted coordinates alone.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem continuous_clampIntervalUnit : Continuous clampIntervalUnit :=
  continuous_const.max (continuous_const.min continuous_id)

theorem continuous_clampComplexSquare : Continuous clampComplexSquare := by
  have hval : clampComplexSquare
      = fun z : ℂ => Complex.ofReal (clampIntervalUnit z.re)
          + Complex.ofReal (clampIntervalUnit z.im) * Complex.I := by
    funext z
    refine Complex.ext ?_ ?_ <;>
      simp [clampComplexSquare, Complex.measurableEquivRealProd_symm_apply]
  rw [hval]
  exact ((Complex.continuous_ofReal.comp
      (continuous_clampIntervalUnit.comp Complex.continuous_re)).add
    ((Complex.continuous_ofReal.comp
      (continuous_clampIntervalUnit.comp Complex.continuous_im)).mul continuous_const))

theorem continuous_boundedRandomEntireCoeff (n : ℕ) :
    Continuous (fun x : ℕ → ℂ => boundedRandomEntireCoeff x n) := by
  rw [show (fun x : ℕ → ℂ => boundedRandomEntireCoeff x n)
      = fun x : ℕ → ℂ => clampComplexSquare (x n) / ((4 : ℂ) * (Nat.factorial n : ℂ)) from rfl]
  exact (continuous_clampComplexSquare.comp (continuous_apply n)).div_const _

theorem continuous_boundedRandomEntire_uncurry :
    Continuous (fun p : (ℕ → ℂ) × ℂ => boundedRandomEntireFunction p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  set R : ℝ := ‖p₀.2‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  set s : Set ((ℕ → ℂ) × ℂ) := Set.univ ×ˢ Metric.ball (0 : ℂ) R with hs
  have hsopen : IsOpen s := isOpen_univ.prod Metric.isOpen_ball
  have hmem : p₀ ∈ s := ⟨Set.mem_univ _, by
    simp only [Metric.mem_ball, dist_zero_right, hR]
    linarith⟩
  have hbound : ∀ n : ℕ, ∀ p ∈ s,
      ‖boundedRandomEntireCoeff p.1 n * p.2 ^ n‖ ≤ R ^ n / (Nat.factorial n : ℝ) := by
    intro n p hp
    have hpR : ‖p.2‖ ≤ R := le_of_lt (by simpa [Metric.mem_ball] using hp.2)
    have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
    rw [norm_mul, norm_pow]
    calc ‖boundedRandomEntireCoeff p.1 n‖ * ‖p.2‖ ^ n
        ≤ (1 / (Nat.factorial n : ℝ)) * R ^ n :=
          mul_le_mul (norm_boundedRandomEntireCoeff_le p.1 n)
            (pow_le_pow_left₀ (norm_nonneg _) hpR n) (by positivity) (by positivity)
      _ = R ^ n / (Nat.factorial n : ℝ) := by field_simp
  have hcont : ContinuousOn (fun p : (ℕ → ℂ) × ℂ => ∑' n : ℕ,
      boundedRandomEntireCoeff p.1 n * p.2 ^ n) s := by
    refine continuousOn_tsum (fun n => ?_) ?_ hbound
    · exact (((continuous_boundedRandomEntireCoeff n).comp continuous_fst).mul
        (continuous_snd.pow n)).continuousOn
    · exact Real.summable_pow_div_factorial R
  exact (hcont.continuousAt (hsopen.mem_nhds hmem))

set_option maxHeartbeats 1000000 in
theorem continuous_boundedRandomEntireSource :
    Continuous (fun x : ℕ → ℂ => boundedRandomEntireSource x) := by
  set cm : (ℕ → ℂ) → C(Fin 1 → ℂ, ℂ) := fun x => (boundedRandomEntireSource x).1 with hcm
  have huncurry : Continuous (Function.uncurry fun x y => (cm x) y) := by
    have h : (Function.uncurry fun (x : ℕ → ℂ) (y : Fin 1 → ℂ) => (cm x) y)
        = fun p : (ℕ → ℂ) × (Fin 1 → ℂ) => boundedRandomEntireFunction p.1 (p.2 0) := by
      funext p
      rfl
    rw [h]
    exact continuous_boundedRandomEntire_uncurry.comp
      (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
  exact continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry cm huncurry)

/-! ### The head–tail decomposition -/

/-- The tail of the clamped series beyond index `N`, as a function of the shifted coordinates. -/
def boundedRandomEntireTail (N : ℕ) (y : ℕ → ℂ) : ℂ → ℂ :=
  fun z => ∑' n : ℕ, clampComplexSquare (y n) / ((4 : ℂ) * (Nat.factorial (n + N) : ℂ)) * z ^ (n + N)

theorem boundedRandomEntireFunction_split (N : ℕ) (x : ℕ → ℂ) (z : ℂ) :
    boundedRandomEntireFunction x z
      = (∑ n ∈ Finset.range N, boundedRandomEntireCoeff x n * z ^ n)
        + boundedRandomEntireTail N (fun k => x (k + N)) z := by
  have hsum : Summable (fun n : ℕ => boundedRandomEntireCoeff x n * z ^ n) :=
    summable_of_orderTwo_bound (boundedRandomEntireCoeff_orderTwo x) z
  rw [boundedRandomEntireFunction, entireOfCoeffs, boundedRandomEntireTail]
  exact (hsum.sum_add_tsum_nat_add N).symm

end

end GaloisForLFunctions.HTGeometry
