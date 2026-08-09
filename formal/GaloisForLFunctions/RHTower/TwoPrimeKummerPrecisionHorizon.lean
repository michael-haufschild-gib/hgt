import GaloisForLFunctions.RHTower.TwoPrimeKummerClockSeparation
import GaloisForLFunctions.HTGeometry.FiniteDiagonalOperator

/-!
# The two-prime Kummer precision horizon

The finite rectangular section of the bounded Kummer phase transform is the diagonal multiplier by
`β(μ) = μ / (1 + |μ|)` over the modes of depth `N`.  Its exact precision data are the Diophantine
approximation profile of the two arithmetic clocks `log 2` and `log 3`:

* `smallestSingularValue_kummerSection` : the least singular value is `d N / (1 + d N)`;
* `inner_normalKummerSection_self_ge` and `normalKummerSection_single` : the constraint-Laplacian
  gap is `(d N / (1 + d N))²`, attained at a coordinate mode;
* `opNorm_kummerSection_inv` : the inverse capacity is `(1 + d N) / d N`;
* `le_opNorm_of_approxLeftInverse_kummerSection` : every fixed-accuracy approximate inverse pays
  the same capacity;
* `tendsto_kummerSectionGap_zero` and `tendsto_kummerSectionInverseCapacity_atTop` : the finite
  gaps vanish and the inverse capacities blow up along the rectangular exhaustion.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The nonzero rectangular source modes of depth `N`. -/
abbrev KummerMode (N : ℕ) := {p : ℤ × ℤ // p ∈ kummerBox N}

theorem kummerMode_nonempty {N : ℕ} (hN : 1 ≤ N) : Nonempty (KummerMode N) := by
  obtain ⟨p, hp⟩ := kummerBox_nonempty hN
  exact ⟨⟨p, hp⟩⟩

/-- The bounded Kummer phase symbol `β(t) = t / (1 + |t|)`. -/
noncomputable def kummerBeta (t : ℝ) : ℝ := t / (1 + |t|)

theorem abs_kummerBeta (t : ℝ) : |kummerBeta t| = |t| / (1 + |t|) := by
  rw [kummerBeta, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |t|)]

theorem kummerBeta_ne_zero {t : ℝ} (ht : t ≠ 0) : kummerBeta t ≠ 0 := by
  rw [kummerBeta]
  exact div_ne_zero ht (by positivity)

/-- The bounded phase profile is increasing on the nonnegative axis. -/
theorem kummerProfile_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    s / (1 + s) ≤ t / (1 + t) := by
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have h2 : (0 : ℝ) < 1 + t := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

/-- The finite Kummer section symbol. -/
noncomputable def kummerSymbol (N : ℕ) (q : KummerMode N) : ℂ :=
  ((kummerBeta (kummerFreq q.1) : ℝ) : ℂ)

theorem norm_kummerSymbol {N : ℕ} (q : KummerMode N) :
    ‖kummerSymbol N q‖ = |kummerFreq q.1| / (1 + |kummerFreq q.1|) := by
  rw [kummerSymbol, Complex.norm_real, Real.norm_eq_abs, abs_kummerBeta]

theorem kummerSymbol_ne_zero {N : ℕ} (hN : 1 ≤ N) (q : KummerMode N) :
    kummerSymbol N q ≠ 0 := by
  rw [kummerSymbol]
  have hfreq : kummerFreq q.1 ≠ 0 := by
    intro h0
    have hlow := kummerFreq_lower_bound hN q.2
    rw [h0, abs_zero] at hlow
    have : (0 : ℝ) < (3 : ℝ) ^ (-(N : ℤ)) := by positivity
    linarith
  exact_mod_cast kummerBeta_ne_zero hfreq

section Section

variable {N : ℕ} [Nonempty (KummerMode N)]

/-- **The exact Kummer precision law.**  The least modulus of the finite section symbol is the
bounded phase profile of the clock separation. -/
theorem diagMin_kummerSymbol (hN : 1 ≤ N) :
    diagMin (kummerSymbol N) = kummerSeparation N / (1 + kummerSeparation N) := by
  obtain ⟨p₀, hp₀, hval⟩ := exists_kummerSeparation_eq hN
  refine le_antisymm ?_ ?_
  · have hle : diagMin (kummerSymbol N) ≤ ‖kummerSymbol N (⟨p₀, hp₀⟩ : KummerMode N)‖ :=
      diagMin_le (kummerSymbol N) (⟨p₀, hp₀⟩ : KummerMode N)
    have hnorm : ‖kummerSymbol N (⟨p₀, hp₀⟩ : KummerMode N)‖
        = |kummerFreq p₀| / (1 + |kummerFreq p₀|) :=
      norm_kummerSymbol (⟨p₀, hp₀⟩ : KummerMode N)
    rw [hnorm, ← hval] at hle
    exact hle
  · refine le_diagMin (kummerSymbol N) (fun q => ?_)
    rw [norm_kummerSymbol]
    exact kummerProfile_mono (kummerSeparation_pos hN).le (kummerSeparation_le q.2)

/-- **Theorem 2.1, least singular value.** -/
theorem smallestSingularValue_kummerSection (hN : 1 ≤ N) :
    smallestSingularValue (diagOp (kummerSymbol N))
      = kummerSeparation N / (1 + kummerSeparation N) := by
  rw [smallestSingularValue_diagOp, diagMin_kummerSymbol hN]

/-- **Theorem 2.1, constraint-Laplacian gap.**  The normal operator of the finite section is
bounded below on the unit sphere by the square of the precision law. -/
theorem inner_normalKummerSection_self_ge (hN : 1 ≤ N)
    (x : EuclideanSpace ℂ (KummerMode N)) (hx : ‖x‖ = 1) :
    (kummerSeparation N / (1 + kummerSeparation N)) ^ 2
      ≤ RCLike.re (inner ℂ ((ContinuousLinearMap.adjoint (diagOp (kummerSymbol N)))
          (diagOp (kummerSymbol N) x)) x) := by
  have h := inner_normalDiagOp_self_ge (kummerSymbol N) x hx
  rwa [diagMin_kummerSymbol hN] at h

omit [Nonempty (KummerMode N)] in
/-- **Theorem 2.1, eigenvalues of the normal operator.**  Every coordinate mode is an eigenvector
with eigenvalue the squared modulus of its symbol. -/
theorem normalKummerSection_single (q : KummerMode N) (c : ℂ) :
    (ContinuousLinearMap.adjoint (diagOp (kummerSymbol N)))
        (diagOp (kummerSymbol N) (EuclideanSpace.single q c))
      = (((|kummerFreq q.1| / (1 + |kummerFreq q.1|)) ^ 2 : ℝ) : ℂ) • EuclideanSpace.single q c := by
  have h := normalDiagOp_single (kummerSymbol N) q c
  rwa [norm_kummerSymbol] at h

/-- **Theorem 2.1, inverse capacity.**  The inverse of the finite section has norm
`(1 + d N) / d N`. -/
theorem opNorm_kummerSection_inv (hN : 1 ≤ N) :
    ‖diagOp (fun q : KummerMode N => (kummerSymbol N q)⁻¹)‖
      = (1 + kummerSeparation N) / kummerSeparation N := by
  rw [opNorm_diagOp_inv (fun q => kummerSymbol_ne_zero hN q), diagMin_kummerSymbol hN]
  rw [inv_div]

omit [Nonempty (KummerMode N)] in
theorem kummerSection_inv_comp (hN : 1 ≤ N) :
    diagOp (fun q : KummerMode N => (kummerSymbol N q)⁻¹) ∘L diagOp (kummerSymbol N)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (KummerMode N)) :=
  diagOp_inv_comp (fun q => kummerSymbol_ne_zero hN q)

omit [Nonempty (KummerMode N)] in
theorem kummerSection_comp_inv (hN : 1 ≤ N) :
    diagOp (kummerSymbol N) ∘L diagOp (fun q : KummerMode N => (kummerSymbol N q)⁻¹)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (KummerMode N)) :=
  diagOp_comp_inv (fun q => kummerSymbol_ne_zero hN q)

/-- **Theorem 4.1, approximate inverse uncertainty law.**  Every `ε`-accurate approximate inverse
of the finite Kummer section pays the same arithmetic capacity. -/
theorem le_opNorm_of_approxLeftInverse_kummerSection (hN : 1 ≤ N)
    (G : EuclideanSpace ℂ (KummerMode N) →L[ℂ] EuclideanSpace ℂ (KummerMode N)) {ε : ℝ}
    (hGB : ‖G ∘L diagOp (kummerSymbol N)
        - ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (KummerMode N))‖ ≤ ε) :
    (1 - ε) * ((1 + kummerSeparation N) / kummerSeparation N) ≤ ‖G‖ := by
  have h := le_opNorm_of_approxLeftInverse (fun q => kummerSymbol_ne_zero hN q) G hGB
  rwa [diagMin_kummerSymbol hN, inv_div] at h

end Section

/-! ## The cofinal horizon -/

/-- The finite-section gap of depth `N`. -/
noncomputable def kummerSectionGap (N : ℕ) : ℝ :=
  kummerSeparation N / (1 + kummerSeparation N)

/-- The finite-section inverse capacity of depth `N`. -/
noncomputable def kummerSectionInverseCapacity (N : ℕ) : ℝ :=
  (1 + kummerSeparation N) / kummerSeparation N

/-- **Theorem 3.1, the elementary window.** -/
theorem kummerSectionGap_window {N : ℕ} (hN : 2 ≤ N) :
    ((3 : ℝ) ^ (-(N : ℤ))) / (1 + (3 : ℝ) ^ (-(N : ℤ))) ≤ kummerSectionGap N ∧
      kummerSectionGap N
        ≤ (Real.log 2 / ((N / 2 : ℕ) : ℝ)) / (1 + Real.log 2 / ((N / 2 : ℕ) : ℝ)) := by
  have hN1 : 1 ≤ N := by omega
  constructor
  · exact kummerProfile_mono (by positivity) (kummerSeparation_lower_bound hN1)
  · exact kummerProfile_mono (kummerSeparation_pos hN1).le (kummerSeparation_upper_bound hN)

/-- **Theorem 3.1, the cofinal horizon.**  The finite-section gaps vanish. -/
theorem tendsto_kummerSectionGap_zero :
    Tendsto kummerSectionGap atTop (𝓝 0) := by
  have hcont : Tendsto (fun t : ℝ => t / (1 + t)) (𝓝 0) (𝓝 0) := by
    have : ContinuousAt (fun t : ℝ => t / (1 + t)) 0 := by
      apply ContinuousAt.div continuousAt_id
      · exact continuousAt_const.add continuousAt_id
      · norm_num
    simpa using this.tendsto
  exact hcont.comp tendsto_kummerSeparation_zero

/-- **Theorem 3.1, capacity blow-up.**  The finite-section inverse capacities diverge. -/
theorem tendsto_kummerSectionInverseCapacity_atTop :
    Tendsto kummerSectionInverseCapacity atTop atTop := by
  have hge : ∀ᶠ N : ℕ in atTop,
      1 / kummerSeparation N ≤ kummerSectionInverseCapacity N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpos := kummerSeparation_pos hN
    rw [kummerSectionInverseCapacity, div_le_div_iff₀ hpos hpos]
    nlinarith
  have hdiv : Tendsto (fun N : ℕ => 1 / kummerSeparation N) atTop atTop := by
    have hpos : ∀ᶠ N : ℕ in atTop, 0 < kummerSeparation N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact kummerSeparation_pos hN
    have hnhds : Tendsto kummerSeparation atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_kummerSeparation_zero, hpos⟩
    have hinv := hnhds.inv_tendsto_nhdsGT_zero
    simpa [Pi.inv_def, one_div] using hinv
  exact tendsto_atTop_mono' atTop hge hdiv

end GaloisForLFunctions.RHTower
