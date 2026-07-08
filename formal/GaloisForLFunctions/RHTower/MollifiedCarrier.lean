/-
The general finite Dirichlet carrier: arbitrary real coefficients on `[1, N]`.

`mollPoly b N = Σ_{n≤N} b_n·n^{−s}` with `b : ℕ → ℝ`, χ-symmetrized to `mollG` and
completed to `completedMollG = archFactor·mollG`.  Real coefficients give Schwarz
reality, the strip FE, and reality on the critical line, exactly as for the sharp
truncation — which is the instance `b ≡ 1`.  The whole critical-line sign-face arc
re-instantiates: termwise decomposition through `carrierLineTerm`, line slope through
`carrierLineSlopeTerm`, slope budget `(Σ|b_n|n^{−1/2})·2(M₁+M₀·log N)`, line sup
`2M₀·Σ|b_n|n^{−1/2}`, anchor bridge, mass floor, and sign bracket.  A mollified carrier
(coefficients a smoothed Möbius convolution) can thus feed the same window machinery as
the sharp carrier, with its anchor faces drawn from mean-value theory at bounded local
variance rather than from the sharp carrier's unbounded one.
-/
import GaloisForLFunctions.RHTower.CarrierMassFloor

open Complex Metric MeasureTheory

namespace RHTower

/-! ### §1 The carrier family -/

/-- The finite Dirichlet polynomial with real coefficients `b` on `[1, N]`. -/
noncomputable def mollPoly (b : ℕ → ℝ) (N : ℕ) : ℂ → ℂ :=
  fun s => ∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * (n : ℂ) ^ (-s)

/-- The χ-symmetrized general carrier `mollG = h + χ·h(1−·)`. -/
noncomputable def mollG (b : ℕ → ℝ) (N : ℕ) : ℂ → ℂ :=
  chiSymmetrize zetaChi (mollPoly b N)

/-- The completed general carrier `archFactor·mollG` — the ξ-shaped object at finite
Euler depth with designed coefficients. -/
noncomputable def completedMollG (b : ℕ → ℝ) (N : ℕ) : ℂ → ℂ :=
  fun s => archFactor s * mollG b N s

/-- The sharp truncation is the instance `b ≡ 1`. -/
theorem mollPoly_one (N : ℕ) : mollPoly (fun _ => 1) N = dirichletPoly N := by
  funext s
  unfold mollPoly dirichletPoly
  simp

/-- The completed sharp carrier is the instance `b ≡ 1` of the completed general
carrier. -/
theorem completedMollG_one (N : ℕ) : completedMollG (fun _ => 1) N = completedGN N := by
  funext s
  unfold completedMollG completedGN mollG gN
  rw [mollPoly_one]

/-! ### §2 Reality -/

private lemma natCast_cpow_conj_mirror (a : ℕ) (s : ℂ) :
    (a : ℂ) ^ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((a : ℂ) ^ s) := by
  have harg : (a : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg a)]
    exact Ne.symm Real.pi_ne_zero
  have h := Complex.cpow_conj (a : ℂ) s harg
  rwa [map_natCast] at h

/-- Schwarz reality of the general Dirichlet polynomial: real coefficients commute with
conjugation. -/
theorem mollPoly_conj (b : ℕ → ℝ) (N : ℕ) (s : ℂ) :
    mollPoly b N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (mollPoly b N s) := by
  unfold mollPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← map_neg, natCast_cpow_conj_mirror]

/-- The exact asymmetric FE of the general carrier, unconditional on the strip. -/
theorem mollG_one_sub (b : ℕ → ℝ) (N : ℕ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mollG b N (1 - s) = zetaChi (1 - s) * mollG b N s :=
  chiSymmetrize_one_sub_at (zetaChi_mul_one_sub_of_mem_strip h0 h1)

/-- Schwarz reality of the general carrier. -/
theorem mollG_conj (b : ℕ → ℝ) (N : ℕ) (s : ℂ) :
    mollG b N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (mollG b N s) := by
  unfold mollG chiSymmetrize
  rw [show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) from by
        rw [map_sub, map_one],
      mollPoly_conj, mollPoly_conj, zetaChi_conj, map_add, map_mul]

/-- The completed general carrier satisfies the exact EVEN functional equation on the
strip. -/
theorem completedMollG_one_sub (b : ℕ → ℝ) (N : ℕ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    completedMollG b N (1 - s) = completedMollG b N s := by
  have hG1 : Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  unfold completedMollG archFactor
  rw [mollG_one_sub b N h0 h1]
  unfold zetaChi
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  field_simp
  ring

/-- Schwarz reality of the completed general carrier. -/
theorem completedMollG_conj (b : ℕ → ℝ) (N : ℕ) (s : ℂ) :
    completedMollG b N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedMollG b N s) := by
  unfold completedMollG archFactor
  rw [Gammaℝ_conj, mollG_conj, map_mul, map_mul, map_div₀, map_mul, map_sub, map_one,
    map_ofNat]

/-- The completed general carrier satisfies the real FE across the critical line, on
the strip. -/
theorem completedMollG_lineReflect (b : ℕ → ℝ) (N : ℕ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    completedMollG b N (lineReflect s) = (starRingEnd ℂ) (completedMollG b N s) := by
  have hc0 : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  have hc1 : ((starRingEnd ℂ) s).re < 1 := by rwa [Complex.conj_re]
  rw [show lineReflect s = 1 - (starRingEnd ℂ) s from rfl,
    completedMollG_one_sub b N hc0 hc1, completedMollG_conj]

/-- Reality of the completed general carrier on the critical line. -/
theorem completedMollG_im_eq_zero_on_line (b : ℕ → ℝ) (N : ℕ) {p : ℂ}
    (hp : p.re = 1 / 2) : (completedMollG b N p).im = 0 :=
  im_eq_zero_on_line_of_realFE hp
    (completedMollG_lineReflect b N (by rw [hp]; norm_num) (by rw [hp]; norm_num))

/-! ### §3 The critical-line decomposition and slope -/

/-- Termwise decomposition of the completed general carrier on the critical line: each
coefficient multiplies the sharp critical-line term. -/
theorem completedMollG_line_term_decomp (b : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    completedMollG b N (linePt u) =
      ∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * carrierLineTerm n u := by
  have h1 : mollPoly b N (linePt u) = ∑ n ∈ Finset.Icc 1 N,
      ((b n : ℝ) : ℂ) * ((((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Real.log n : ℂ)) * u)) := by
    unfold mollPoly
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [natCast_cpow_neg_linePt n (Finset.mem_Icc.mp hn).1 u]
  have h2 : mollPoly b N (1 - linePt u) = ∑ n ∈ Finset.Icc 1 N,
      ((b n : ℝ) : ℂ) * ((((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((-Real.log n : ℝ) : ℂ)) * u)) := by
    unfold mollPoly
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [natCast_cpow_neg_one_sub_linePt n (Finset.mem_Icc.mp hn).1 u]
  show archFactor (linePt u) * mollG b N (linePt u) = _
  unfold mollG chiSymmetrize carrierLineTerm
  rw [h1, h2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Line slope of the completed general carrier: coefficients multiply the sharp
termwise slopes. -/
private noncomputable def mollLineSlope (b : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * carrierLineSlopeTerm n u

/-- The completed general carrier is differentiable along the critical line. -/
private theorem hasDerivAt_completedMollG_line (b : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => completedMollG b N (linePt v)) (mollLineSlope b N u) u := by
  have hfun : (fun v : ℝ => completedMollG b N (linePt v)) =
      fun v : ℝ => ∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * carrierLineTerm n v :=
    funext fun v => completedMollG_line_term_decomp b N v
  have hpi : (∑ n ∈ Finset.Icc 1 N,
        fun v : ℝ => ((b n : ℝ) : ℂ) * carrierLineTerm n v) =
      fun v : ℝ => ∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * carrierLineTerm n v := by
    funext v
    simp
  rw [hfun, ← hpi]
  exact HasDerivAt.sum fun n _ => (hasDerivAt_carrierLineTerm n u).const_mul _

/-- The real part of the completed general carrier is differentiable along the critical
line. -/
private theorem hasDerivAt_re_completedMollG_line (b : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => (completedMollG b N (linePt v)).re)
      ((mollLineSlope b N u).re) u := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
    (hasDerivAt_completedMollG_line b N u)
  simpa using h

/-! ### §4 Closed-form budgets -/

/-- The carrier weight `Σ_{n≤N} |b_n|·n^{−1/2}` — the coefficient mass seen by every
critical-line budget. -/
noncomputable def mollWeight (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |b n| * ((n : ℝ) ^ (-(1/2 : ℝ)))

theorem mollWeight_nonneg (b : ℕ → ℝ) (N : ℕ) : 0 ≤ mollWeight b N :=
  Finset.sum_nonneg fun n _ =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- For the sharp instance the weight is the square-root telescope. -/
theorem mollWeight_one_le (N : ℕ) : mollWeight (fun _ => 1) N ≤ 2 * Real.sqrt N := by
  unfold mollWeight
  simpa using sum_rpow_neg_half_le N

/-- The line-slope budget of the general carrier: `mollWeight·2(M₁ + M₀·log N)`. -/
noncomputable def mollSlopeLineBudget (b : ℕ → ℝ) (N : ℕ) (M₀ M₁ : ℝ) : ℝ :=
  mollWeight b N * (2 * (M₁ + M₀ * Real.log N))

/-- **Closed-form slope bound for the general carrier**: envelope sups `M₀`, `M₁` on
both sides of the reflection bound the critical-line slope by the slope budget. -/
private theorem norm_mollLineSlope_le (b : ℕ → ℝ) (N : ℕ) {u M₀ M₁ : ℝ}
    (hM₀ : ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁) :
    ‖mollLineSlope b N u‖ ≤ mollSlopeLineBudget b N M₀ M₁ := by
  unfold mollLineSlope mollSlopeLineBudget mollWeight
  calc ‖∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * carrierLineSlopeTerm n u‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖((b n : ℝ) : ℂ) * carrierLineSlopeTerm n u‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          |b n| * (((n : ℝ) ^ (-(1/2 : ℝ))) * (2 * (M₁ + M₀ * Real.log N))) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_carrierLineSlopeTerm_le (Finset.mem_Icc.mp hn).1
            (Finset.mem_Icc.mp hn).2 hM₀ hM₀r hM₁ hM₁r)
          (abs_nonneg _)
    _ = (∑ n ∈ Finset.Icc 1 N, |b n| * ((n : ℝ) ^ (-(1/2 : ℝ)))) *
          (2 * (M₁ + M₀ * Real.log N)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun n _ => by ring

/-- Termwise line sup: the general Dirichlet polynomial is bounded by its weight on the
critical line. -/
private theorem norm_mollPoly_line_le (b : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    ‖mollPoly b N (linePt u)‖ ≤ mollWeight b N := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖((b n : ℝ) : ℂ) * (n : ℂ) ^ (-(linePt u))‖ =
        |b n| * ((n : ℝ) ^ (-(1/2 : ℝ))) := by
    intro n hn
    have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    congr 1
    rw [Complex.neg_re, linePt_re]
  unfold mollPoly mollWeight
  calc ‖∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * (n : ℂ) ^ (-(linePt u))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖((b n : ℝ) : ℂ) * (n : ℂ) ^ (-(linePt u))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, |b n| * ((n : ℝ) ^ (-(1/2 : ℝ))) :=
        Finset.sum_congr rfl hterm

/-- Line sup for the χ-symmetrized general carrier: `‖mollG‖ ≤ 2·mollWeight` — the
reflected part is a conjugate and χ is unimodular on the line. -/
private theorem norm_mollG_line_le (b : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    ‖mollG b N (linePt u)‖ ≤ 2 * mollWeight b N := by
  have hrefl : ‖mollPoly b N (1 - linePt u)‖ = ‖mollPoly b N (linePt u)‖ := by
    rw [← conj_linePt, mollPoly_conj, Complex.norm_conj]
  have hd := norm_mollPoly_line_le b N u
  calc ‖mollG b N (linePt u)‖
      = ‖mollPoly b N (linePt u) +
          zetaChi (linePt u) * mollPoly b N (1 - linePt u)‖ := rfl
    _ ≤ ‖mollPoly b N (linePt u)‖ +
          ‖zetaChi (linePt u) * mollPoly b N (1 - linePt u)‖ := norm_add_le _ _
    _ = ‖mollPoly b N (linePt u)‖ + ‖mollPoly b N (linePt u)‖ := by
        rw [norm_mul, norm_zetaChi_line, one_mul, hrefl]
    _ ≤ 2 * mollWeight b N := by linarith

/-- Line sup for the completed general carrier from an envelope sup. -/
private theorem abs_re_completedMollG_line_le (b : ℕ → ℝ) (N : ℕ) {u M₀ : ℝ}
    (hM₀ : ‖archFactor (linePt u)‖ ≤ M₀) :
    |(completedMollG b N (linePt u)).re| ≤ M₀ * (2 * mollWeight b N) := by
  refine le_trans (Complex.abs_re_le_norm _) ?_
  calc ‖completedMollG b N (linePt u)‖
      = ‖archFactor (linePt u)‖ * ‖mollG b N (linePt u)‖ := norm_mul _ _
    _ ≤ M₀ * (2 * mollWeight b N) :=
        mul_le_mul hM₀ (norm_mollG_line_le b N u) (norm_nonneg _)
          (le_trans (norm_nonneg _) hM₀)

/-! ### §5 Anchor, mass floor, and sign bracket -/

/-- On the critical line the completed general carrier is real, so its real part
carries the full modulus. -/
private theorem abs_re_completedMollG_line_eq_norm (b : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    |(completedMollG b N (linePt u)).re| = ‖completedMollG b N (linePt u)‖ := by
  have him : (completedMollG b N (linePt u)).im = 0 :=
    completedMollG_im_eq_zero_on_line b N (by rw [linePt_re])
  have hz : completedMollG b N (linePt u) =
      (((completedMollG b N (linePt u)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [him])
  conv_rhs => rw [hz]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- Anchor bridge for the general carrier: an archimedean floor times a carrier floor
is a pointwise floor for `|Re|` on the line. -/
theorem anchor_re_completedMollG_line_of_floors (b : ℕ → ℝ) (N : ℕ) {τ a₀ m : ℝ}
    (hm0 : 0 ≤ m)
    (ha₀ : a₀ ≤ ‖archFactor (linePt τ)‖)
    (hm : m ≤ ‖mollG b N (linePt τ)‖) :
    a₀ * m ≤ |(completedMollG b N (linePt τ)).re| := by
  rw [abs_re_completedMollG_line_eq_norm]
  calc a₀ * m ≤ ‖archFactor (linePt τ)‖ * ‖mollG b N (linePt τ)‖ :=
        mul_le_mul ha₀ hm hm0 (norm_nonneg _)
    _ = ‖completedMollG b N (linePt τ)‖ := (norm_mul _ _).symm

/-- **Short-interval mass floor for the general carrier**: an anchor at the window
center and envelope sups produce the second-moment floor through the point-to-mass
converter. -/
private theorem sq_integral_re_completedMollG_line_floor_of_anchor (b : ℕ → ℝ) (N : ℕ)
    {τ rz c M₀ M₁ : ℝ} (hrz : 0 < rz) (hc : 0 < c)
    (hD : 0 < mollSlopeLineBudget b N M₀ M₁)
    (hM₀ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hanchor : c ≤ |(completedMollG b N (linePt τ)).re|) :
    (c / 2) ^ 2 * (2 * min rz (c / (2 * mollSlopeLineBudget b N M₀ M₁))) ≤
      ∫ u in (τ - rz)..(τ + rz), ((completedMollG b N (linePt u)).re) ^ 2 :=
  sq_integral_floor_of_anchor_slope hrz hc hD
    (fun u _ => hasDerivAt_re_completedMollG_line b N u)
    (fun u hu =>
      le_trans (Complex.abs_re_le_norm _)
        (norm_mollLineSlope_le b N (hM₀ u hu) (hM₀r u hu) (hM₁ u hu) (hM₁r u hu)))
    hanchor

/-- **Sign bracket for the general carrier from anchor and slope data**: in a window
carrying a center anchor, envelope sups, a line sup, and a first moment strictly below
the anchor-generated mass floor, the completed general carrier changes sign. -/
theorem exists_completedMollG_sign_bracket_of_anchor_slope (b : ℕ → ℝ) (N : ℕ)
    {τ rz c M₀ M₁ M_line : ℝ} (hrz : 0 < rz) (hc : 0 < c)
    (hD : 0 < mollSlopeLineBudget b N M₀ M₁)
    (hM₀ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc (τ - rz) (τ + rz), ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hanchor : c ≤ |(completedMollG b N (linePt τ)).re|)
    (hsup : ∀ u ∈ Set.Icc (τ - rz) (τ + rz),
      |(completedMollG b N (linePt u)).re| ≤ M_line)
    (hfm : M_line * |∫ u in (τ - rz)..(τ + rz), (completedMollG b N (linePt u)).re| <
      (c / 2) ^ 2 * (2 * min rz (c / (2 * mollSlopeLineBudget b N M₀ M₁)))) :
    ∃ t₁ t₂ : ℝ, t₁ ∈ Set.Icc (τ - rz) (τ + rz) ∧ t₂ ∈ Set.Icc (τ - rz) (τ + rz) ∧
      t₁ ≤ t₂ ∧
      (completedMollG b N (linePt t₁)).re * (completedMollG b N (linePt t₂)).re ≤ 0 := by
  have hmin0 : 0 < min rz (c / (2 * mollSlopeLineBudget b N M₀ M₁)) :=
    lt_min hrz (by positivity)
  have hcont : ContinuousOn (fun u : ℝ => (completedMollG b N (linePt u)).re)
      (Set.Icc (τ - rz) (τ + rz)) :=
    fun u _ => (hasDerivAt_re_completedMollG_line b N u).continuousAt.continuousWithinAt
  exact exists_sign_bracket_of_moment_gap (by linarith) hcont (by positivity)
    (sq_integral_re_completedMollG_line_floor_of_anchor b N hrz hc hD
      hM₀ hM₀r hM₁ hM₁r hanchor)
    hsup hfm

end RHTower
