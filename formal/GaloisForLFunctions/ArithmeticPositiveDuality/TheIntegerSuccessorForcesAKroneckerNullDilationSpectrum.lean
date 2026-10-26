import GaloisForLFunctions.ArithmeticPositiveDuality.ArchimedeanPositiveDefiniteFunctionsLiveOnTheKroneckerLine
import GaloisForLFunctions.ArithmeticPositiveDuality.TheBostConnesTemperatureIsTheHeckeExponent

/-!
# The integer successor forces a Kronecker-null dilation spectrum

The spectral measure of a positive-definite function on `ℚ_{>0}` lives on the prime torus; the
archimedean characters `u ↦ u^{ix}` form the Kronecker line `x ↦ z_x` in it. Archimedean
functions are carried by that line (`spectralMeasure_eq_map_archPoint`). The arithmetic
successors push the dilation spectrum off it.

* **Decay detects the line** (`spectralMeasure_range_archPoint_eq_zero`). If
  `f((N+b)/(N+a)) → 0` as `N → ∞` for all `a ≠ b`, every spectral measure of `f` gives zero mass
  to the Kronecker line. The `M`-point Gram form at `(N+j)/N`, `j < M`, equals `f(1)/M + o(1)`,
  while its part on the line is `∫ |M⁻¹Σ_j ((N+j)/N)^{ix}|² dν(x) → ν(ℝ)`.
* **Integer and Bost–Connes successors** (`integer_successor_kronecker_null`,
  `bc_successor_kronecker_null`). The Hecke law `nd|f(u)|² ≤ 1` (and `(nd)^β|f(u)|² ≤ 1`) gives the
  decay: `(N+b)/(N+a)` has height `nd ≥ N²/(a − b)²`.
* **Dichotomy** (`eq_zero_of_archimedean_le_integer_successor`). A dilation part forced by the
  integer successor dominates no nonzero archimedean positive-definite function: if
  `f − g` is positive definite and `g(u) = G(log u)` with `G` continuous, then `g = 0`.

So the integer successor and every archimedean dilation correlation, Weil's included, are
spectrally singular on the prime torus: they meet in no positive-definite component.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The positive rational `(N + 1 + b)/(N + 1 + a)`. -/
def nearUnit (N a b : ℕ) : posUnits :=
  ⟨Units.mk0 (((N + 1 + b : ℕ) : ℚ) / ((N + 1 + a : ℕ) : ℚ)) (by positivity), by
    show (0 : ℚ) < ((N + 1 + b : ℕ) : ℚ) / ((N + 1 + a : ℕ) : ℚ); positivity⟩

theorem val_nearUnit (N a b : ℕ) :
    (((nearUnit N a b : posUnits) : ℚˣ) : ℚ) = ((N + 1 + b : ℕ) : ℚ) / ((N + 1 + a : ℕ) : ℚ) :=
  rfl

/-- `(N+1+b)/(N+1+a)` has height `nd ≥ (N+1)²/(a − b)²`. -/
theorem sq_le_index_nearUnit (N a b : ℕ) (hab : a ≠ b) :
    ((N : ℝ) + 1) ^ 2 ≤ ((a : ℝ) - b) ^ 2 *
      (((((nearUnit N a b : posUnits) : ℚˣ) : ℚ).num.natAbs : ℝ) *
        ((((nearUnit N a b : posUnits) : ℚˣ) : ℚ).den : ℝ)) := by
  set q : ℚ := (((nearUnit N a b : posUnits) : ℚˣ) : ℚ) with hq
  set A : ℕ := N + 1 + b
  set B : ℕ := N + 1 + a
  have hB : (0 : ℚ) < B := by positivity
  have hq0 : 0 < q := (nearUnit N a b).2
  have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq0.le)
  -- cross-multiplication `n·B = A·d`
  have hcross : (q.num.natAbs : ℝ) * B = A * q.den := by
    have h1 : q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
    have h2 : q = (A : ℚ) / B := by rw [hq, val_nearUnit]
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    have h3 : (q.num : ℚ) * B = A * q.den := by
      rw [h1] at h2
      field_simp at h2
      linarith
    have h4 : ((q.num.natAbs : ℤ) : ℚ) * B = A * q.den := by rw [hnum]; exact h3
    exact_mod_cast h4
  have hnd : q.num.natAbs ≠ q.den := by
    intro h
    have : (A : ℝ) = B := by
      have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      rw [h] at hcross
      nlinarith
    have : A = B := by exact_mod_cast this
    omega
  have hgap : 1 ≤ |(q.num.natAbs : ℝ) - q.den| := by
    have : (q.num.natAbs : ℤ) - q.den ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnd)
    have h1 : (1 : ℤ) ≤ |(q.num.natAbs : ℤ) - q.den| := Int.one_le_abs this
    exact_mod_cast h1
  -- `(n − d)B = (A − B)d`
  have hdiff : ((q.num.natAbs : ℝ) - q.den) * B = ((A : ℝ) - B) * q.den := by
    linarith [hcross]
  have hAB : ((A : ℝ) - B) = (b : ℝ) - a := by simp only [A, B]; push_cast; ring
  have hdpos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hApos : (0 : ℝ) < A := by positivity
  have hBd : (B : ℝ) ≤ |(a : ℝ) - b| * q.den := by
    have := congrArg abs hdiff
    rw [abs_mul, abs_mul, abs_of_pos hBpos, abs_of_pos hdpos, hAB] at this
    rw [abs_sub_comm (a : ℝ) b]
    nlinarith [hgap, this]
  have hAn : (A : ℝ) ≤ |(a : ℝ) - b| * q.num.natAbs := by
    have : (A : ℝ) * q.den ≤ |(a : ℝ) - b| * q.num.natAbs * q.den := by
      have h := mul_le_mul_of_nonneg_left hBd (Nat.cast_nonneg (q.num.natAbs) : (0 : ℝ) ≤ _)
      nlinarith [hcross]
    exact le_of_mul_le_mul_right this hdpos
  have hNA : (N : ℝ) + 1 ≤ A := by
    simp only [A]; push_cast; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hNB : (N : ℝ) + 1 ≤ B := by
    simp only [B]; push_cast; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have hsq : ((a : ℝ) - b) ^ 2 = |(a : ℝ) - b| ^ 2 := (sq_abs _).symm
  rw [hsq]
  calc ((N : ℝ) + 1) ^ 2 ≤ (A : ℝ) * B := by nlinarith
    _ ≤ (|(a : ℝ) - b| * q.num.natAbs) * (|(a : ℝ) - b| * q.den) :=
        mul_le_mul hAn hBd hBpos.le (by positivity)
    _ = |(a : ℝ) - b| ^ 2 * ((q.num.natAbs : ℝ) * q.den) := by ring

/-- Heights of `(N+1+b)/(N+1+a)` grow: a weight bounded by a negative power of the height
tends to `0` along them. -/
theorem tendsto_of_index_bound {f : posUnits → ℂ} {β C : ℝ} (hβ : 0 < β)
    (hf : ∀ u : posUnits, (((u : ℚˣ) : ℚ).num.natAbs * ((u : ℚˣ) : ℚ).den : ℝ) ^ β *
      Complex.normSq (f u) ≤ C) (a b : ℕ) (hab : a ≠ b) :
    Tendsto (fun N => f (nearUnit N a b)) atTop (𝓝 0) := by
  have hab' : (0 : ℝ) < ((a : ℝ) - b) ^ 2 := by
    have : (a : ℝ) ≠ b := by exact_mod_cast hab
    positivity
  set L : ℕ → ℝ := fun N => ((N : ℝ) + 1) ^ 2 / ((a : ℝ) - b) ^ 2 with hL
  have hLpos : ∀ N, 0 < L N := fun N => by positivity
  have hLH : ∀ N, L N ≤ (((((nearUnit N a b : posUnits) : ℚˣ) : ℚ).num.natAbs : ℝ) *
      ((((nearUnit N a b : posUnits) : ℚˣ) : ℚ).den : ℝ)) := fun N => by
    rw [hL, div_le_iff₀ hab', mul_comm]
    exact sq_le_index_nearUnit N a b hab
  have hbound : ∀ N, ‖f (nearUnit N a b)‖ ^ 2 ≤ C / L N ^ β := fun N => by
    rw [← Complex.normSq_eq_norm_sq, le_div_iff₀ (Real.rpow_pos_of_pos (hLpos N) β)]
    calc Complex.normSq (f (nearUnit N a b)) * L N ^ β
        ≤ Complex.normSq (f (nearUnit N a b)) *
          (((((nearUnit N a b : posUnits) : ℚˣ) : ℚ).num.natAbs : ℝ) *
            ((((nearUnit N a b : posUnits) : ℚˣ) : ℚ).den : ℝ)) ^ β :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hLpos N).le (hLH N) hβ.le)
            (Complex.normSq_nonneg _)
      _ ≤ C := by rw [mul_comm]; exact hf _
  have hLtop : Tendsto L atTop atTop := by
    refine Tendsto.atTop_div_const hab' ?_
    exact (tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun N => C / L N ^ β) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hβ).comp hLtop)
  have h2 : Tendsto (fun N => ‖f (nearUnit N a b)‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity) hbound hlim
  have h1 : Tendsto (fun N => ‖f (nearUnit N a b)‖) atTop (𝓝 0) := by
    have := h2.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h1

/-! ### Decay detects the Kronecker line -/

/-- The points `(N+1+j)/(N+1)`. -/
def nearPoint (N : ℕ) (j : ℕ) : posUnits := nearUnit N 0 j

theorem nearPoint_inv_mul (N a b : ℕ) :
    (nearPoint N a)⁻¹ * nearPoint N b = nearUnit N a b := by
  refine Subtype.ext (Units.ext ?_)
  simp only [nearPoint, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [val_nearUnit, val_nearUnit, val_nearUnit]
  push_cast
  field_simp

theorem nearUnit_self (N a : ℕ) : nearUnit N a a = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [val_nearUnit, div_self (by positivity)]
  rfl

theorem tendsto_log_nearPoint (j : ℕ) :
    Tendsto (fun N => Real.log ((((nearPoint N j : posUnits) : ℚˣ) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have hval : ∀ N : ℕ, ((((nearPoint N j : posUnits) : ℚˣ) : ℚ) : ℝ) = 1 + j / ((N : ℝ) + 1) :=
    fun N => by
      rw [nearPoint, val_nearUnit]
      push_cast
      simp only [add_zero]
      field_simp
  simp_rw [hval]
  have h0 : Tendsto (fun N : ℕ => (1 : ℝ) + j / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    have h1 := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (j : ℝ)).const_add (1 : ℝ)
    rw [mul_zero, add_zero] at h1
    exact h1.congr fun N => by ring
  have := ((Real.continuousAt_log one_ne_zero).tendsto).comp h0
  rwa [Real.log_one] at this

/-- **Decay along `(N+b)/(N+a)` gives a Kronecker-null spectrum.** If `f((N+b)/(N+a)) → 0` for all
`a ≠ b`, every finite measure on the prime torus representing `f` gives zero mass to the Kronecker
line. -/
theorem spectralMeasure_range_archPoint_eq_zero {f : posUnits → ℂ} {μ : Measure PrimeTorus}
    [IsFiniteMeasure μ] (hμ : ∀ u : posUnits, f u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ)
    (hdecay : ∀ a b : ℕ, a ≠ b → Tendsto (fun N => f (nearUnit N a b)) atTop (𝓝 0)) :
    μ (range archPoint) = 0 := by
  set ν : Measure ℝ := μ.comap archPoint with hν_def
  have hνuniv : ν univ = μ (range archPoint) := by
    rw [hν_def, measurableEmbedding_archPoint.comap_apply, Set.image_univ]
  haveI : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_lt_top _ _⟩
  have hM : ∀ M : ℕ, 0 < M → ν.real univ ≤ (f 1).re / M := by
    intro M hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    set c : Fin M → ℂ := fun _ => (1 / M : ℂ) with hc
    set Φ : ℕ → PrimeTorus → ℝ := fun N x =>
      Complex.normSq (∑ b : Fin M, c b * ratChar ((nearPoint N b : ℚˣ) : ℚ) x) with hΦ
    set G : ℕ → ℂ := fun N => ∑ a : Fin M, ∑ b : Fin M,
      star (c a) * f ((nearPoint N a)⁻¹ * nearPoint N b) * c b with hG
    set Ival : ℕ → ℝ := fun N => ∫ t, Φ N (archPoint t) ∂ν with hIval
    -- the Gram value dominates its part on the line
    have hGI : ∀ N, Ival N ≤ (G N).re := by
      intro N
      have hg := gram_integral_ratChar μ (fun b : Fin M => nearPoint N b) c
      have hGe : G N = ((∫ x, Φ N x ∂μ : ℝ) : ℂ) := by
        rw [← hg]
        simp only [hG, hμ]
      rw [hGe, Complex.ofReal_re]
      have hcont : Continuous (Φ N) := Complex.continuous_normSq.comp
        (continuous_finsetSum _ fun b _ => continuous_const.mul (continuous_ratChar _))
      have hint : Integrable (Φ N) μ :=
        hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      calc Ival N = ∫ x in range archPoint, Φ N x ∂μ := by
            rw [← measurableEmbedding_archPoint.map_comap μ,
              measurableEmbedding_archPoint.integral_map]
        _ ≤ ∫ x, Φ N x ∂μ :=
            setIntegral_le_integral hint (Eventually.of_forall fun _ => Complex.normSq_nonneg _)
    -- the Gram value tends to `f(1)/M`
    have hGlim : Tendsto G atTop (𝓝 (f 1 / M)) := by
      have hterm : ∀ a b : Fin M, Tendsto
          (fun N => star (c a) * f ((nearPoint N a)⁻¹ * nearPoint N b) * c b) atTop
          (𝓝 (if a = b then star (c a) * f 1 * c b else 0)) := by
        intro a b
        simp_rw [nearPoint_inv_mul]
        by_cases hab : a = b
        · subst hab
          simp only [nearUnit_self, if_true]
          exact tendsto_const_nhds
        · rw [if_neg hab]
          have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
          simpa using ((hdecay a b hab').const_mul (star (c a))).mul_const (c b)
      have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin M)) fun a _ =>
        tendsto_finsetSum (Finset.univ : Finset (Fin M)) fun b _ => hterm a b
      convert hsum using 2
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, hc, star_div₀, star_one,
        star_natCast, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    -- the part on the line tends to `ν(ℝ)`
    have hIlim : Tendsto Ival atTop (𝓝 (ν.real univ)) := by
      have hpt : ∀ t, Tendsto (fun N => Φ N (archPoint t)) atTop (𝓝 1) := by
        intro t
        have hterm : ∀ b : Fin M, Tendsto (fun N => c b *
            ratChar (((nearPoint N b : posUnits) : ℚˣ) : ℚ) (archPoint t)) atTop (𝓝 (c b * 1)) := by
          intro b
          simp_rw [ratChar_archPoint]
          refine tendsto_const_nhds.mul ?_
          have h0 := tendsto_log_nearPoint b
          have := (Complex.continuous_exp.tendsto _).comp
            ((((Complex.continuous_ofReal.tendsto _).comp h0).mul_const (t : ℂ)).mul_const I)
          simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at this
          exact this
        have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin M)) fun b _ => hterm b
        have hone : ∑ b : Fin M, c b * 1 = 1 := by
          simp only [hc, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp
        rw [hone] at hsum
        have := (Complex.continuous_normSq.tendsto _).comp hsum
        rw [Complex.normSq_one] at this
        exact this
      have hdom : ∀ N, ∀ᵐ t ∂ν, ‖Φ N (archPoint t)‖ ≤ 1 := fun N =>
        Eventually.of_forall fun t => by
          rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
          have hle : ‖∑ b : Fin M, c b *
              ratChar (((nearPoint N b : posUnits) : ℚˣ) : ℚ) (archPoint t)‖ ≤ 1 := by
            calc _ ≤ ∑ b : Fin M,
                  ‖c b * ratChar (((nearPoint N b : posUnits) : ℚˣ) : ℚ) (archPoint t)‖ :=
                  norm_sum_le _ _
              _ = ∑ _b : Fin M, (1 / M : ℝ) := by
                refine Finset.sum_congr rfl fun b _ => ?_
                rw [norm_mul, ratChar_archPoint, Complex.norm_exp]
                simp [hc]
              _ = 1 := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                field_simp
          have := pow_le_pow_left₀ (norm_nonneg _) hle 2
          simpa using this
      have h := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun N => ((Complex.continuous_normSq.comp (continuous_finsetSum _ fun b _ =>
          continuous_const.mul (continuous_ratChar _))).comp continuous_archPoint).aestronglyMeasurable)
        (integrable_const 1) hdom (Eventually.of_forall hpt)
      rw [integral_const, smul_eq_mul, mul_one] at h
      exact h
    have hre : Tendsto (fun N => (G N).re) atTop (𝓝 ((f 1).re / M)) := by
      have := (Complex.continuous_re.tendsto _).comp hGlim
      simp only [Complex.div_natCast_re] at this
      exact this
    exact le_of_tendsto_of_tendsto' hIlim hre hGI
  -- conclude
  have hzero : ν.real univ = 0 := by
    refine le_antisymm ?_ measureReal_nonneg
    by_contra hpos
    push Not at hpos
    obtain ⟨M, hM'⟩ := exists_nat_gt ((f 1).re / ν.real univ)
    have hM1 : 0 < M + 1 := Nat.succ_pos M
    have h := hM (M + 1) hM1
    have hMp : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hM1
    rw [le_div_iff₀ hMp] at h
    rw [div_lt_iff₀ hpos] at hM'
    push_cast at h
    nlinarith
  rw [← hνuniv]
  rw [measureReal_def] at hzero
  exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right (measure_ne_top _ _)

/-! ### The arithmetic successors -/

/-- The dilation part of a function on `Aff(ℚ)`, as a function on `ℚ_{>0}`. -/
def dilationPart (φ : AffineGroupQ → ℂ) (u : posUnits) : ℂ := φ (dilation (u : ℚˣ))

theorem isPosDefOnGroup_dilationPart {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) :
    IsPosDefOnGroup (dilationPart φ) :=
  hφ.comp_hom (dilation.comp posUnits.subtype)

/-- **The integer successor forces a Kronecker-null dilation spectrum.** For a positive-definite
`φ` on `Aff(ℚ)` with successor `1_ℤ`, every spectral measure of its dilation part gives zero mass
to the Kronecker line. -/
theorem integer_successor_kronecker_null {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hs : HasIntegerSuccessor φ) {μ : Measure PrimeTorus} [IsFiniteMeasure μ]
    (hμ : ∀ u : posUnits, dilationPart φ u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ) :
    μ (range archPoint) = 0 :=
  spectralMeasure_range_archPoint_eq_zero hμ fun a b hab =>
    tendsto_of_index_bound (β := 1) (C := 1) one_pos
      (fun u => by rw [Real.rpow_one]; exact normSq_dilation_le hφ hs (u : ℚˣ)) a b hab

/-- **Bost–Connes successors force Kronecker-null dilation spectra.** -/
theorem bc_successor_kronecker_null {β : ℝ} (hβ : 1 < β) {φ : AffineGroupQ → ℂ}
    (hφ : IsPosDefOnGroup φ) (hs : ∀ b, φ (translation b) = bcSuccessor β b)
    {μ : Measure PrimeTorus} [IsFiniteMeasure μ]
    (hμ : ∀ u : posUnits, dilationPart φ u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ) :
    μ (range archPoint) = 0 :=
  spectralMeasure_range_archPoint_eq_zero hμ fun a b hab =>
    tendsto_of_index_bound (β := β) (C := 1) (by linarith) (fun u => by
      have h := (bc_successor_hecke_exponent hβ).1 φ hφ hs (u : ℚˣ)
      have hpos : (0 : ℝ) < (((u : ℚˣ) : ℚ).num.natAbs * ((u : ℚˣ) : ℚ).den : ℝ) := by
        have := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (u : ℚˣ).ne_zero)
        have := ((u : ℚˣ) : ℚ).den_pos
        positivity
      rw [Real.rpow_neg hpos.le] at h
      rw [dilationPart]
      calc _ ≤ (((u : ℚˣ) : ℚ).num.natAbs * ((u : ℚˣ) : ℚ).den : ℝ) ^ β *
            ((((u : ℚˣ) : ℚ).num.natAbs * ((u : ℚˣ) : ℚ).den : ℝ) ^ β)⁻¹ :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos β).ne') a b hab

/-- **Dichotomy.** The dilation part of a positive-definite function with integer successor
dominates no nonzero archimedean positive-definite function: if `g(u) = G(log u)` with `G`
continuous and both `g` and `f − g` are positive definite, then `g = 0`. -/
theorem eq_zero_of_archimedean_le_integer_successor {φ : AffineGroupQ → ℂ}
    (hφ : IsPosDefOnGroup φ) (hs : HasIntegerSuccessor φ) {g : posUnits → ℂ}
    (hg : IsPosDefOnGroup g) {G : ℝ → ℂ} (hG : Continuous G)
    (hgG : ∀ u : posUnits, g u = G (Real.log ((u : ℚˣ) : ℚ)))
    (hfg : IsPosDefOnGroup fun u => dilationPart φ u - g u) (u : posUnits) : g u = 0 := by
  obtain ⟨μg, hμg, hgμ⟩ := exists_measure_ratChar hg
  obtain ⟨μh, hμh, hhμ⟩ := exists_measure_ratChar hfg
  have hsum : ∀ v : posUnits, dilationPart φ v = ∫ x, ratChar ((v : ℚˣ) : ℚ) x ∂(μg + μh) := by
    intro v
    rw [integral_add_measure (integrable_ratChar _ _) (integrable_ratChar _ _), ← hgμ v, ← hhμ v]
    ring
  have hnull := integer_successor_kronecker_null hφ hs hsum
  have hg_line : μg (range archPoint) = 0 := by
    have h : μg (range archPoint) ≤ (μg + μh) (range archPoint) := by
      rw [Measure.add_apply]; exact le_self_add
    rw [hnull] at h
    exact le_antisymm h zero_le
  have hg_off := spectralMeasure_compl_range_archPoint hg hG hgG hgμ
  have h0 : μg = 0 := by
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self (range archPoint)]
    exact measure_union_null hg_line hg_off
  rw [hgμ u, h0, integral_zero_measure]

end GaloisForLFunctions.ArithmeticPositiveDuality
