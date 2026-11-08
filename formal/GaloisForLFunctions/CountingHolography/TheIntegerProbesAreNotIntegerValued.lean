import GaloisForLFunctions.ArithmeticScatteringHolography.TheIntegerProbesOfTheHorizon
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWeilKernelHasInfinitelyManyPositiveSquares
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-!
# The Krein squares of the integer probes are not integers

The Krein square of an integer probe `a ∈ ℤ^N` is `Q(a) = W(f_a, f_a)` with
`f_a = Σ_i a_i B(· − log(i + 1))` (`integerProbe`). If every `Q(a)` were an integer, `Q` itself
would be an `ℤ`-valued count and the count door over `ℤ` would be open. It is not:

**Theorem** (`not_integerProbe_integerValued`). Some integer probe has a Krein square that is not an
integer.

**Proof.**
* The Gram entries are values of the spline series `F(t) = Σ_ρ e^{t(ρ−½)} w_ρ`,
  `w_ρ = W_ρ(B, B)`, at `t = log((i+1)/(j+1))` (`atomGram_eq_splineSeries`).
* Integer squares at `e_i` and `e_i + e_j` put `2 Re F(log(m/n))` in `ℤ` for all `m, n ≥ 1`
  (`two_re_splineSeries_mem`). The scales `log(m/n)` are dense and `F` is continuous, so `2 Re F` is
  integer-valued on `ℝ`, hence constant (`re_splineSeries_eq_const`).
* A bounded spline orbit has zero width `0`: RH (`riemannHypothesis_of_re_splineSeries_bdd`).
* Under RH every zero is critical, `w_ρ = m_ρ |B̂(γ)|² ≥ 0`, and
  `Re F(0) − Re F(t) = Σ_ρ w_ρ (1 − cos γ_ρ t)`. The spline sees a critical zero `γ₁`
  (`RenormalizedIntersectionTheory.criticalSeen_infinite`), and at `t = π/γ₁` the sum is at least
  `2 w_{ρ₁} > 0` (`re_splineSeries_zero_sub_ge`): `Re F` is not constant.

The same holds for any integral trace form: no kernel `C : ℕ × ℕ → ℤ`, e.g. the traces
`Tr(T_m T_nᵗ)` of Hecke endomorphisms of a free abelian group, reproduces `Q` on the integer probes
(`not_exists_intKernel_eq_integerProbe`).

So integrality of the probes is refuted unconditionally, and its only route to a contradiction runs
through RH: integer values would make the spline orbit constant, hence bounded, hence RH, and RH
makes the orbit a nonconstant Bohr series with nonnegative weights. A count with Tate limit `Q`
must be a genuine limit, not the form itself.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate Real
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
  GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)
open GaloisForLFunctions.ArithmeticScatteringHolography (atomGram integerProbe atomGram_isHermitian
  atomGram_im)
open GaloisForLFunctions.RenormalizedIntersectionTheory (splineSeries continuous_splineSeries
  orbitCorr_splineCycle_eq criticalSeen criticalSeen_infinite
  cx_cubicSpline_contDiff cx_cubicSpline_hasCompactSupport)

noncomputable section

namespace GaloisForLFunctions.CountingHolography

/-! ### The Gram entries are values of the spline series -/

/-- **The Gram entries of the integer probes are the spline series at the log-distance.** -/
theorem atomGram_eq_splineSeries (N : ℕ) (i j : Fin N) :
    atomGram N i j = splineSeries (Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1)) := by
  have h1 : atomGram N i j = ArithmeticPositiveDuality.splineCorr
      (Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1)) :=
    ArithmeticPositiveDuality.weilGram_translate_cubicSpline
      (fun k : Fin N => Real.log ((k : ℝ) + 1)) i j
  rw [h1]
  set y := Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1)
  have hW : ArithmeticPositiveDuality.splineCorr y =
      zetaZeroConfig.W (ArithmeticCastelnuovoSeveri.translate y (cx cubicSpline)) (cx cubicSpline) := by
    rw [RHTower.zeta_W_eq_weilFullFunctional_mixed (ArithmeticCastelnuovoSeveri.translate_contDiff cx_cubicSpline_contDiff y)
      (ArithmeticCastelnuovoSeveri.translate_hasCompactSupport cx_cubicSpline_hasCompactSupport y) cx_cubicSpline_contDiff
      cx_cubicSpline_hasCompactSupport]
    rfl
  have h0 : cx cubicSpline = ArithmeticCastelnuovoSeveri.translate 0 (cx cubicSpline) := funext fun v => by
    simp [ArithmeticCastelnuovoSeveri.translate]
  have h2 : zetaZeroConfig.W (ArithmeticCastelnuovoSeveri.translate y (cx cubicSpline)) (cx cubicSpline) =
      zetaZeroConfig.W (ArithmeticCastelnuovoSeveri.translate y (cx cubicSpline))
        (ArithmeticCastelnuovoSeveri.translate 0 (cx cubicSpline)) := by rw [← h0]
  rw [hW, h2, W_shiftTest_shiftTest, splineSeries]
  refine tsum_congr fun τ => ?_
  simp only [Complex.ofReal_zero, sub_zero]

/-- The zero-side terms of the spline series are absolutely summable at every scale. -/
theorem summable_norm_splineTerm' (t : ℝ) :
    Summable fun τ : zetaZeroConfig.carrier =>
      ‖cexp ((t : ℂ) * ((τ : ℂ) - 1 / 2)) * zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) τ‖ := by
  have hsum := summable_norm_Wsummand zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)
  refine (hsum.mul_left (Real.exp (|t| / 2))).of_nonneg_of_le (fun _ => norm_nonneg _) fun τ => ?_
  have hstrip := zetaZeroConfig.strip τ.1 τ.2
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre : ((t : ℂ) * ((τ : ℂ) - 1 / 2)).re = t * ((τ : ℂ).re - 1 / 2) := by simp
  rw [hre]
  have h1 : |(τ : ℂ).re - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  calc t * ((τ : ℂ).re - 1 / 2) ≤ |t * ((τ : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |t| * |(τ : ℂ).re - 1 / 2| := abs_mul _ _
    _ ≤ |t| * (1 / 2) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |t| / 2 := by ring

/-! ### Integer squares force a constant orbit -/

/-- The Krein square as a real quadratic form in the (real) Gram entries. -/
theorem integerProbe_eq_sum (N : ℕ) (a : Fin N → ℤ) :
    integerProbe N a = ∑ i : Fin N, ∑ j : Fin N, (atomGram N i j).re * (a i : ℝ) * (a j : ℝ) := by
  unfold integerProbe HTGeometry.hermQuad
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, map_intCast,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  set r : ℝ := (atomGram N i j).re
  have hreal : atomGram N i j = (r : ℂ) :=
    Complex.ext rfl (by simpa using atomGram_im N i j)
  have hcast : (a i : ℂ) * (atomGram N i j * (a j : ℂ)) =
      ((r * (a i : ℝ) * (a j : ℝ) : ℝ) : ℂ) := by
    rw [hreal]; push_cast; ring
  rw [hcast, Complex.ofReal_re]

theorem integerProbe_single (N : ℕ) (i : Fin N) :
    integerProbe N (Pi.single i 1) = (atomGram N i i).re := by
  rw [integerProbe_eq_sum]
  simp [Pi.single_apply]

theorem integerProbe_pair (N : ℕ) (i j : Fin N) :
    integerProbe N (Pi.single i 1 + Pi.single j 1) =
      (atomGram N i i).re + (atomGram N j j).re + 2 * (atomGram N i j).re := by
  have hji : (atomGram N j i).re = (atomGram N i j).re := by
    have hH : starRingEnd ℂ (atomGram N j i) = atomGram N i j :=
      congr_fun (congr_fun (atomGram_isHermitian N) i) j
    have := congr_arg Complex.re hH
    simpa using this
  rw [integerProbe_eq_sum]
  simp only [Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hji]
  ring

/-- **Integer squares put `2 Re F` in `ℤ` at every rational log-scale.** -/
theorem two_re_splineSeries_mem (hint : ∀ (N : ℕ) (a : Fin N → ℤ), ∃ k : ℤ, integerProbe N a = k)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ k : ℤ, 2 * (splineSeries (Real.log m - Real.log n)).re = k := by
  set N := max m n + 1
  have hmN : m - 1 < N := by omega
  have hnN : n - 1 < N := by omega
  set i : Fin N := ⟨m - 1, hmN⟩
  set j : Fin N := ⟨n - 1, hnN⟩
  have hi : ((i : ℕ) : ℝ) + 1 = m := by
    simp only [i]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hj : ((j : ℕ) : ℝ) + 1 = n := by
    simp only [j]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hii : (atomGram N i i).re = (splineSeries 0).re := by
    rw [atomGram_eq_splineSeries, sub_self]
  have hjj : (atomGram N j j).re = (splineSeries 0).re := by
    rw [atomGram_eq_splineSeries, sub_self]
  obtain ⟨k₁, hk₁⟩ := hint N (Pi.single i 1)
  rw [integerProbe_single, hii] at hk₁
  obtain ⟨k₂, hk₂⟩ := hint N (Pi.single i 1 + Pi.single j 1)
  rw [integerProbe_pair N i j, hii, hjj, atomGram_eq_splineSeries, hi, hj, hk₁] at hk₂
  exact ⟨k₂ - 2 * k₁, by push_cast; linarith⟩

/-- **Integer squares make the real part of the spline series constant.** -/
theorem re_splineSeries_eq_const (hint : ∀ (N : ℕ) (a : Fin N → ℤ), ∃ k : ℤ, integerProbe N a = k)
    (t : ℝ) : (splineSeries t).re = (splineSeries 0).re := by
  set f : ℝ → ℝ := fun t => 2 * (splineSeries t).re with hfdef
  have hf : Continuous f := continuous_const.mul (Complex.continuous_re.comp continuous_splineSeries)
  have hclosed : IsClosed (Set.range (Int.cast : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isClosed_range
  -- integer values at the rational log-scales
  have hrat : ∀ q : ℚ, 0 < q → f (Real.log q) ∈ Set.range (Int.cast : ℤ → ℝ) := by
    intro q hq
    have hnum : 0 < q.num := Rat.num_pos.mpr hq
    have hnum' : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      have : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have hlog : Real.log (q : ℝ) = Real.log (q.num.toNat : ℕ) - Real.log (q.den : ℕ) := by
      rw [← Real.log_div (by rw [hnum']; exact_mod_cast hnum.ne')
        (by exact_mod_cast q.den_ne_zero), hnum']
      congr 1
      exact_mod_cast (Rat.num_div_den q).symm
    obtain ⟨k, hk⟩ := two_re_splineSeries_mem hint (m := q.num.toNat) (n := q.den) (by omega)
      q.den_pos
    exact ⟨k, by simp only [hfdef]; rw [hlog]; exact hk.symm⟩
  -- every value is an integer
  have hall : ∀ s, f s ∈ Set.range (Int.cast : ℤ → ℝ) := by
    intro s
    by_contra hs
    have hopen : IsOpen (f ⁻¹' (Set.range (Int.cast : ℤ → ℝ))ᶜ) := hclosed.isOpen_compl.preimage hf
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen s hs
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show Real.exp s < Real.exp (s + δ / 2) from Real.exp_lt_exp.mpr (by linarith))
    have hqpos : (0 : ℝ) < q := (Real.exp_pos s).trans hq1
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hqpos
    have h1 : s < Real.log q := by rw [Real.lt_log_iff_exp_lt hqpos]; exact hq1
    have h2 : Real.log q < s + δ / 2 := by rw [Real.log_lt_iff_lt_exp hqpos]; exact hq2
    have hmem : Real.log q ∈ Metric.ball s δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    exact hball hmem (hrat q hq0)
  -- an integer-valued continuous function on `ℝ` is constant
  by_contra hne
  obtain ⟨k₀, hk₀⟩ := hall 0
  obtain ⟨k₁, hk₁⟩ := hall t
  have hk : k₀ ≠ k₁ := by
    intro h
    apply hne
    have : f t = f 0 := by rw [← hk₀, ← hk₁, h]
    simp only [hfdef] at this
    linarith
  -- a half-integer between the two values is attained
  set v : ℝ := if k₀ < k₁ then (k₀ : ℝ) + 1 / 2 else (k₀ : ℝ) - 1 / 2
  have hv : v ∈ Set.uIcc (f 0) (f t) := by
    rw [← hk₀, ← hk₁]
    rcases lt_or_gt_of_ne hk with h | h
    · have h' : (k₀ : ℝ) + 1 ≤ k₁ := by exact_mod_cast h
      simp only [v, if_pos h]
      exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
    · have h' : (k₁ : ℝ) + 1 ≤ k₀ := by exact_mod_cast h
      simp only [v, if_neg (not_lt.mpr h.le)]
      exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hf.continuousOn hv
  obtain ⟨k, hk'⟩ := hall s
  rw [← hk'] at hs
  by_cases h : k₀ < k₁
  · simp only [v, if_pos h] at hs
    have : (2 * k : ℤ) = 2 * k₀ + 1 := by
      have : (2 * k : ℝ) = 2 * k₀ + 1 := by linarith
      exact_mod_cast this
    omega
  · simp only [v, if_neg h] at hs
    have : (2 * k : ℤ) = 2 * k₀ - 1 := by
      have : (2 * k : ℝ) = 2 * k₀ - 1 := by linarith
      exact_mod_cast this
    omega

/-- **A bounded spline orbit is RH.** -/
theorem riemannHypothesis_of_re_splineSeries_bdd {C : ℝ} (h : ∀ t, |(splineSeries t).re| ≤ C) :
    RiemannHypothesis := by
  have hrate : SquareRootThreshold.zetaZeroWidth ≤ 0 := by
    refine (zeta_splineOrbit_rate_iff_zetaZeroWidth_le le_rfl).mp ⟨C, fun t _ => ?_⟩
    rw [zero_mul, Real.exp_zero, mul_one, orbitCorr_splineCycle_eq]
    exact h t
  exact SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
    (le_antisymm hrate SquareRootThreshold.zetaZeroWidth_nonneg)

/-! ### Under RH the orbit is a Bohr series with nonnegative weights -/

/-- On the critical line the spline weight is `m_ρ |B̂(γ)|²`. -/
theorem Wsummand_cubicSpline_of_re {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ =
      (((zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (cx cubicSpline) (ρ.im : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have hγ : gammaOf ρ = (ρ.im : ℂ) := by
    rw [show ρ = 1 / 2 + (ρ.im : ℂ) * I from Complex.ext (by simp [hre]) (by simp), gammaOf]
    apply Complex.ext <;> simp
  simp only [ZeroConfig.Wsummand, hγ, conj_ofReal, mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The weight `m_ρ |B̂(γ_ρ)|²` of a critical zero. -/
def criticalWeight (ρ : ℂ) : ℝ := (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (cx cubicSpline) (ρ.im : ℂ)‖ ^ 2

theorem re_splineTerm_of_re {ρ : ℂ} (hre : ρ.re = 1 / 2) (t : ℝ) :
    (cexp ((t : ℂ) * (ρ - 1 / 2)) * zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ).re =
      criticalWeight ρ * Real.cos (t * ρ.im) := by
  have hρ : ρ - 1 / 2 = (ρ.im : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
  rw [hρ, Wsummand_cubicSpline_of_re hre,
    show (t : ℂ) * ((ρ.im : ℂ) * I) = ((t * ρ.im : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, criticalWeight]
  ring

/-- **Under RH the spline orbit is not constant.** -/
theorem exists_re_splineSeries_lt (hRH : RiemannHypothesis) :
    ∃ t, (splineSeries t).re < (splineSeries 0).re := by
  have hline := RHTower.CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
  -- a critical zero seen by the spline, off the real point `1/2`
  obtain ⟨ρ₁, hρ₁, hne⟩ : ∃ ρ ∈ criticalSeen, ρ ≠ 1 / 2 := by
    obtain ⟨ρ, hρ⟩ := (criticalSeen_infinite.sdiff (Set.finite_singleton (1 / 2 : ℂ))).nonempty
    exact ⟨ρ, hρ.1, fun h => hρ.2 (Set.mem_singleton_iff.mpr h)⟩
  obtain ⟨hcar, hre₁, hseen⟩ := hρ₁
  have him : ρ₁.im ≠ 0 := by
    intro h
    exact hne (Complex.ext (by simp [hre₁]) (by simp [h]))
  have hw₁ : 0 < criticalWeight ρ₁ := by
    have hm : (1 : ℝ) ≤ zetaZeroConfig.mult ρ₁ := by exact_mod_cast zetaZeroConfig.one_le_mult ρ₁ hcar
    unfold criticalWeight
    exact mul_pos (by linarith) (pow_pos (norm_pos_iff.mpr hseen) 2)
  set t₁ : ℝ := π / ρ₁.im
  refine ⟨t₁, ?_⟩
  -- the real parts as real series
  have hsum : ∀ t : ℝ, Summable fun τ : zetaZeroConfig.carrier =>
      cexp ((t : ℂ) * ((τ : ℂ) - 1 / 2)) * zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) τ :=
    fun t => (summable_norm_splineTerm' t).of_norm
  have hre : ∀ t : ℝ, (splineSeries t).re =
      ∑' τ : zetaZeroConfig.carrier, criticalWeight τ * Real.cos (t * (τ : ℂ).im) := by
    intro t
    rw [splineSeries, Complex.re_tsum (hsum t)]
    exact tsum_congr fun τ => re_splineTerm_of_re (hline τ τ.2) t
  have hsr : ∀ t : ℝ, Summable fun τ : zetaZeroConfig.carrier =>
      criticalWeight τ * Real.cos (t * (τ : ℂ).im) := fun t => by
    refine ((hsum t).mapL Complex.reCLM).congr fun τ => ?_
    exact re_splineTerm_of_re (hline τ τ.2) t
  -- the difference is a sum of nonnegative terms, one of which is `2 w₁`
  set g : zetaZeroConfig.carrier → ℝ := fun τ =>
    criticalWeight τ * Real.cos (0 * (τ : ℂ).im) - criticalWeight τ * Real.cos (t₁ * (τ : ℂ).im)
  have hg : Summable g := (hsr 0).sub (hsr t₁)
  have hdiff : (splineSeries 0).re - (splineSeries t₁).re = ∑' τ, g τ := by
    rw [hre, hre, ← (hsr 0).tsum_sub (hsr t₁)]
  have hnonneg : ∀ τ, 0 ≤ g τ := fun τ => by
    have hw : 0 ≤ criticalWeight τ := by unfold criticalWeight; positivity
    simp only [g, zero_mul, Real.cos_zero, mul_one]
    nlinarith [Real.cos_le_one (t₁ * (τ : ℂ).im)]
  have hτ₁ : g ⟨ρ₁, hcar⟩ = 2 * criticalWeight ρ₁ := by
    simp only [g, zero_mul, Real.cos_zero, mul_one]
    rw [show t₁ * ρ₁.im = π by simp only [t₁]; field_simp, Real.cos_pi]
    ring
  have hle := hg.le_tsum ⟨ρ₁, hcar⟩ fun τ _ => hnonneg τ
  rw [hτ₁] at hle
  linarith

/-! ### The theorem -/

/-- **The Krein squares of the integer probes are not all integers.** -/
theorem not_integerProbe_integerValued :
    ¬ ∀ (N : ℕ) (a : Fin N → ℤ), ∃ k : ℤ, integerProbe N a = k := by
  intro hint
  have hconst := re_splineSeries_eq_const hint
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_re_splineSeries_bdd (C := |(splineSeries 0).re|) fun t => by rw [hconst t]
  obtain ⟨t, ht⟩ := exists_re_splineSeries_lt hRH
  rw [hconst t] at ht
  exact lt_irrefl _ ht

/-- **No `ℤ`-valued count equals the Krein square of the integer probes.** -/
theorem not_exists_intCount_eq_integerProbe :
    ¬ ∃ K : ∀ N, (Fin N → ℤ) → ℤ, ∀ N a, integerProbe N a = K N a :=
  fun ⟨K, hK⟩ => not_integerProbe_integerValued fun N a => ⟨K N a, hK N a⟩

/-- **No integral trace form is the Weil form of the integer probes.** No kernel `C : ℕ × ℕ → ℤ`
(for instance `C(m, n) = Tr(T_m T_nᵗ)` for endomorphisms `T_n` of a free abelian group of finite
rank) has `Σ C(i+1, j+1) a_i a_j = Q(a)` on every integer probe. -/
theorem not_exists_intKernel_eq_integerProbe :
    ¬ ∃ C : ℕ → ℕ → ℤ, ∀ (N : ℕ) (a : Fin N → ℤ),
      integerProbe N a = ((∑ i : Fin N, ∑ j : Fin N, C (i + 1) (j + 1) * a i * a j : ℤ) : ℝ) :=
  fun ⟨C, hC⟩ => not_integerProbe_integerValued fun N a => ⟨_, hC N a⟩

end GaloisForLFunctions.CountingHolography
