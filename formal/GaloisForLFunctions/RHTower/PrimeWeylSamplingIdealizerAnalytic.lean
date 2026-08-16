import GaloisForLFunctions.HTGeometry.JetTestFunctions
import GaloisForLFunctions.RHTower.SuperlinearSamplingAperiodicity

/-!
# The analytic sampling idealizer of the finite shift–Weyl algebra

A finite shift–Weyl operator on the Schwartz space of the line is a finite sum

`Q = ∑_{h ∈ F} ∑_{j ≤ m} a_{h,j}(ξ) ∂_ξ^j S_h`,   `(S_h φ)(ξ) = φ(ξ + h)`,

with complex polynomial coefficients.  For a set `S ⊆ ℝ` the sampling ideal is the space of
Schwartz functions vanishing on `S`, and `Q` belongs to the sampling idealizer when it maps that
ideal into itself.

If `S` is locally finite, symmetric and has superlinear counting growth, then the idealizer is
exactly the algebra of polynomial multipliers: every coefficient attached to a nonzero shift and
every coefficient attached to a positive derivative order vanishes.

The separation mechanism is a translated jet atom: a monomial centred at a point, cut off inside a
radius so small that the resulting compactly supported smooth function vanishes on all of `S` and
at every other shifted evaluation point, while realising one prescribed derivative there.  Its
coefficient is then read off directly, and a polynomial with infinitely many real roots is zero.
The infinitude of shift failures comes from superlinear aperiodicity.
-/

namespace RHTower

open Set Metric GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Jet atoms centred at a point -/

/-- The `j`-th jet atom at `y` with cutoff radius `ε`: the normalised monomial `(x-y)^j/j!` cut off
outside the ball of radius `2ε`. -/
def jetAtom (y ε : ℝ) (j : ℕ) : ℝ → ℂ :=
  fun x => (cutoffScaled ε (x - y) : ℝ) • (((x - y : ℝ) : ℂ) ^ j / (Nat.factorial j : ℂ))

theorem contDiff_jetAtom (y ε : ℝ) (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (jetAtom y ε j) := by
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x - y) := contDiff_id.sub contDiff_const
  exact ((contDiff_cutoffScaled ε).comp hsub).smul
    (((contDiff_ofReal_pow j).comp hsub).div_const _)

theorem jetAtom_eq_zero_of_far {y ε : ℝ} (hε : 0 < ε) (j : ℕ) {x : ℝ} (hx : 2 * ε ≤ |x - y|) :
    jetAtom y ε j x = 0 := by
  rw [jetAtom, cutoffScaled_eq_zero hε hx, zero_smul]

theorem hasCompactSupport_jetAtom {y ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    HasCompactSupport (jetAtom y ε j) := by
  refine HasCompactSupport.intro (isCompact_closedBall y (2 * ε)) fun x hx => ?_
  refine jetAtom_eq_zero_of_far hε j ?_
  rw [mem_closedBall, Real.dist_eq] at hx
  exact le_of_lt (not_le.mp hx)

/-- Near its centre the jet atom is exactly the normalised monomial. -/
theorem jetAtom_eventuallyEq {y ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    jetAtom y ε j =ᶠ[nhds y] fun x : ℝ => ((x - y : ℝ) : ℂ) ^ j / (Nat.factorial j : ℂ) := by
  have hopen : IsOpen {x : ℝ | |x - y| < ε} :=
    isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const
  have hmem : {x : ℝ | |x - y| < ε} ∈ nhds y := hopen.mem_nhds (by simpa using hε)
  filter_upwards [hmem] with x hx
  rw [jetAtom, cutoffScaled_eq_one hε (le_of_lt hx), one_smul]

theorem iteratedDeriv_congr_nhds {f g : ℝ → ℂ} {x : ℝ} (h : f =ᶠ[nhds x] g) (i : ℕ) :
    iteratedDeriv i f x = iteratedDeriv i g x := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    (Filter.EventuallyEq.iteratedFDeriv ℝ h i).eq_of_nhds]

theorem iteratedDeriv_ofReal_pow_div_factorial_zero (i j : ℕ) :
    iteratedDeriv i (fun x : ℝ => ((x : ℂ)) ^ j / (Nat.factorial j : ℂ)) 0
      = if i = j then 1 else 0 := by
  have hdiv : (fun x : ℝ => ((x : ℂ)) ^ j / (Nat.factorial j : ℂ))
      = ((Nat.factorial j : ℂ)⁻¹) • (fun x : ℝ => ((x : ℂ)) ^ j) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hcd : ContDiffAt ℝ (i : ℕ∞) (fun x : ℝ => ((x : ℂ)) ^ j) 0 :=
    ((contDiff_ofReal_pow j).of_le (by exact_mod_cast le_top)).contDiffAt
  have hfac : ((Nat.factorial j : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero j
  rw [hdiv, iteratedDeriv_const_smul hcd, iteratedDeriv_ofReal_pow_zero]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, smul_eq_mul, inv_mul_cancel₀ hfac]
  · rw [if_neg h, if_neg h, smul_zero]

/-- **The jet atoms realise the Kronecker delta at their centre.** -/
theorem iteratedDeriv_jetAtom_self {y ε : ℝ} (hε : 0 < ε) (i j : ℕ) :
    iteratedDeriv i (jetAtom y ε j) y = if i = j then 1 else 0 := by
  rw [iteratedDeriv_congr_nhds (jetAtom_eventuallyEq hε j) i]
  have hcomp : (fun x : ℝ => ((x - y : ℝ) : ℂ) ^ j / (Nat.factorial j : ℂ))
      = fun x : ℝ => (fun t : ℝ => ((t : ℂ)) ^ j / (Nat.factorial j : ℂ)) (x - y) := rfl
  have hshift : iteratedDeriv i (fun x : ℝ =>
        (fun t : ℝ => ((t : ℂ)) ^ j / (Nat.factorial j : ℂ)) (x - y))
      = fun t : ℝ => iteratedDeriv i (fun t : ℝ => ((t : ℂ)) ^ j / (Nat.factorial j : ℂ)) (t - y) :=
    iteratedDeriv_comp_sub_const i (fun t : ℝ => ((t : ℂ)) ^ j / (Nat.factorial j : ℂ)) y
  rw [hcomp, hshift]
  simp only [sub_self]
  rw [iteratedDeriv_ofReal_pow_div_factorial_zero]

/-- Away from its cutoff ball the jet atom has vanishing derivatives of every order. -/
theorem iteratedDeriv_jetAtom_far {y ε : ℝ} (hε : 0 < ε) (j : ℕ) {z : ℝ} (hz : 2 * ε < |z - y|)
    (i : ℕ) : iteratedDeriv i (jetAtom y ε j) z = 0 := by
  have hopen : IsOpen {x : ℝ | 2 * ε < |x - y|} :=
    isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
  have hev : jetAtom y ε j =ᶠ[nhds z] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds hz] with x hx
    exact jetAtom_eq_zero_of_far hε j (le_of_lt hx)
  rw [iteratedDeriv_congr_nhds hev i, iteratedDeriv_const]
  simp

/-- The jet atom as a Schwartz function. -/
def jetAtomSchwartz (y : ℝ) {ε : ℝ} (hε : 0 < ε) (j : ℕ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_jetAtom hε j).toSchwartzMap
    (by exact_mod_cast contDiff_jetAtom y ε j)

@[simp]
theorem jetAtomSchwartz_coe (y : ℝ) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ((jetAtomSchwartz y hε j : SchwartzMap ℝ ℂ) : ℝ → ℂ) = jetAtom y ε j := rfl

theorem jetAtomSchwartz_apply (y : ℝ) {ε : ℝ} (hε : 0 < ε) (j : ℕ) (x : ℝ) :
    (jetAtomSchwartz y hε j : ℝ → ℂ) x = jetAtom y ε j x := rfl

/-! ## The finite shift–Weyl algebra and its sampling idealizer -/

/-- Evaluation of the finite shift–Weyl operator with polynomial coefficients `a` at `x`. -/
def shiftWeylEval (m : ℕ) (F : Finset ℝ) (a : ℝ → ℕ → Polynomial ℂ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ h ∈ F, ∑ j ∈ Finset.range (m + 1), (a h j).eval (x : ℂ) * iteratedDeriv j φ (x + h)

/-- The operator maps every Schwartz function vanishing on `S` to a function vanishing on `S`. -/
def PreservesSamplingIdeal (m : ℕ) (S : Set ℝ) (F : Finset ℝ) (a : ℝ → ℕ → Polynomial ℂ) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ, (∀ γ ∈ S, (φ : ℝ → ℂ) γ = 0) →
    ∀ γ ∈ S, shiftWeylEval m F a (φ : ℝ → ℂ) γ = 0

/-! ## Separation inside a locally finite sampling set -/

/-- Around any point, a locally finite sampling set together with a finite set of auxiliary points
admits a punctured ball avoiding both. -/
theorem exists_separating_radius {S : Set ℝ} (hlf : LocallyFiniteSamples S) (y : ℝ)
    (A : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ z ∈ S, z ≠ y → 2 * ε < |z - y|) ∧ (∀ z ∈ A, z ≠ y → 2 * ε < |z - y|) := by
  classical
  set B : Finset ℝ := (((hlf (|y| + 1)).toFinset ∪ A).erase y) with hB
  have hdpos : ∃ d : ℝ, 0 < d ∧ ∀ z ∈ B, d ≤ |z - y| := by
    rcases B.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun z hz => absurd hz (by rw [hemp]; exact Finset.notMem_empty z)⟩
    · refine ⟨B.inf' hne (fun z => |z - y|), ?_, fun z hz => Finset.inf'_le _ hz⟩
      rw [Finset.lt_inf'_iff]
      intro z hz
      have hzy : z ≠ y := Finset.ne_of_mem_erase hz
      exact abs_pos.mpr (sub_ne_zero.mpr hzy)
  obtain ⟨d, hd, hdB⟩ := hdpos
  refine ⟨min d 1 / 3, by positivity, ?_, ?_⟩
  · intro z hzS hzy
    by_cases hzw : |z| ≤ |y| + 1
    · have hzB : z ∈ B := by
        refine Finset.mem_erase.mpr ⟨hzy, Finset.mem_union_left _ ?_⟩
        refine (hlf (|y| + 1)).mem_toFinset.mpr ⟨hzS, ?_⟩
        rw [Set.mem_Icc]
        constructor <;> [skip; skip] <;> cases abs_le.mp hzw <;> linarith
      have := hdB z hzB
      have hmin : min d 1 ≤ d := min_le_left _ _
      linarith
    · have hlow : |y| + 1 < |z| := not_le.mp hzw
      have habs : |z| - |y| ≤ |z - y| := abs_sub_abs_le_abs_sub z y
      have hmin : min d 1 ≤ 1 := min_le_right _ _
      linarith
  · intro z hzA hzy
    have hzB : z ∈ B := Finset.mem_erase.mpr ⟨hzy, Finset.mem_union_right _ hzA⟩
    have := hdB z hzB
    have hmin : min d 1 ≤ d := min_le_left _ _
    linarith

/-! ## Collapse of the nonzero-shift and positive-order coefficients -/

/-- The operator applied to a jet atom, evaluated at the shifted centre, reads off exactly one
polynomial coefficient. -/
theorem shiftWeylEval_jetAtom {m : ℕ} {F : Finset ℝ} {a : ℝ → ℕ → Polynomial ℂ}
    {γ y ε : ℝ} (hε : 0 < ε) {h : ℝ} (hhF : h ∈ F) (hy : γ + h = y) {j : ℕ} (hj : j ≤ m)
    (hsep : ∀ h' ∈ F, h' ≠ h → 2 * ε < |γ + h' - y|) :
    shiftWeylEval m F a (jetAtom y ε j) γ = (a h j).eval (γ : ℂ) := by
  classical
  rw [shiftWeylEval, Finset.sum_eq_single h]
  · rw [Finset.sum_eq_single j]
    · rw [hy, iteratedDeriv_jetAtom_self hε j j, if_pos rfl, mul_one]
    · intro k _ hkj
      rw [hy, iteratedDeriv_jetAtom_self hε k j, if_neg hkj, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · intro h' hh' hne
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [iteratedDeriv_jetAtom_far hε j (hsep h' hh' hne) k, mul_zero]
  · intro hnot
    exact absurd hhF hnot

/-- If a shift misses the sampling set at infinitely many samples, every polynomial coefficient
attached to it vanishes. -/
theorem shiftCoeff_eq_zero_of_infinite_failure {m : ℕ} {S : Set ℝ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ} (hlf : LocallyFiniteSamples S)
    (hpres : PreservesSamplingIdeal m S F a)
    {h : ℝ} (hhF : h ∈ F) (hfail : (shiftFailure S h).Infinite) {j : ℕ} (hj : j ≤ m) :
    a h j = 0 := by
  classical
  refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
  refine Set.Infinite.mono (s := (fun γ : ℝ => (γ : ℂ)) '' shiftFailure S h) ?_
    (hfail.image (Complex.ofReal_injective.injOn))
  rintro _ ⟨γ, ⟨hγS, hγh⟩, rfl⟩
  obtain ⟨ε, hε, hεS, hεA⟩ :=
    exists_separating_radius hlf (γ + h) (F.image fun h' => γ + h')
  have hnull : ∀ z ∈ S, ((jetAtomSchwartz (γ + h) hε j : SchwartzMap ℝ ℂ) : ℝ → ℂ) z = 0 := by
    intro z hz
    rw [jetAtomSchwartz_coe]
    have hzy : z ≠ γ + h := fun hzeq => hγh (hzeq ▸ hz)
    exact jetAtom_eq_zero_of_far hε j (le_of_lt (hεS z hz hzy))
  have hzero := hpres (jetAtomSchwartz (γ + h) hε j) hnull γ hγS
  rw [jetAtomSchwartz_coe,
    shiftWeylEval_jetAtom hε hhF rfl hj
      (fun h' hh' hne => hεA _ (Finset.mem_image.mpr ⟨h', hh', rfl⟩)
        (fun heq => hne (add_left_cancel heq)))] at hzero
  exact hzero

/-- On an infinite sampling set every positive-order coefficient at the zero shift vanishes. -/
theorem derivCoeff_eq_zero_of_infinite_samples {m : ℕ} {S : Set ℝ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ} (hlf : LocallyFiniteSamples S)
    (hpres : PreservesSamplingIdeal m S F a)
    (h0 : (0 : ℝ) ∈ F) (hS : S.Infinite) {j : ℕ} (hj : j ≤ m) (hj0 : j ≠ 0) :
    a 0 j = 0 := by
  classical
  refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
  refine Set.Infinite.mono (s := (fun γ : ℝ => (γ : ℂ)) '' S) ?_
    (hS.image (Complex.ofReal_injective.injOn))
  rintro _ ⟨γ, hγS, rfl⟩
  obtain ⟨ε, hε, hεS, hεA⟩ := exists_separating_radius hlf γ (F.image fun h' => γ + h')
  have hnull : ∀ z ∈ S, ((jetAtomSchwartz γ hε j : SchwartzMap ℝ ℂ) : ℝ → ℂ) z = 0 := by
    intro z hz
    rw [jetAtomSchwartz_coe]
    by_cases hzy : z = γ
    · rw [hzy, jetAtom, sub_self, Complex.ofReal_zero, zero_pow hj0, zero_div, smul_zero]
    · exact jetAtom_eq_zero_of_far hε j (le_of_lt (hεS z hz hzy))
  have hzero := hpres (jetAtomSchwartz γ hε j) hnull γ hγS
  rw [jetAtomSchwartz_coe,
    shiftWeylEval_jetAtom hε h0 (add_zero γ) hj
      (fun h' hh' hne => hεA _ (Finset.mem_image.mpr ⟨h', hh', rfl⟩)
        (fun heq => hne (by linarith [heq])))] at hzero
  exact hzero

/-! ## Theorem A -/

theorem infinite_of_superlinearSamples {S : Set ℝ} (hsuper : SuperlinearSamples S) : S.Infinite := by
  intro hfin
  obtain ⟨T, hT, hlt⟩ := hsuper (hfin.toFinset.card + 1 : ℕ)
  have hsub : samplingCount S T ≤ hfin.toFinset.card := by
    rw [samplingCount, Set.ncard_eq_toFinset_card _ (hfin.subset Set.inter_subset_left)]
    exact Finset.card_le_card (by
      intro x hx
      exact hfin.mem_toFinset.mpr ((hfin.subset Set.inter_subset_left).mem_toFinset.mp hx).1)
  have hcard : ((hfin.toFinset.card : ℕ) : ℝ) + 1 ≤ ((hfin.toFinset.card : ℕ) + 1 : ℕ) * T := by
    push_cast
    nlinarith [hT, Nat.cast_nonneg (α := ℝ) hfin.toFinset.card]
  have : ((samplingCount S T : ℕ) : ℝ) ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast hsub
  linarith

/-- **Theorem A: the sampling idealizer of the finite shift–Weyl algebra collapses.**  For a
locally finite symmetric sampling set of superlinear counting growth, every coefficient of an
operator preserving the sampling ideal vanishes except the zero-shift, zero-order polynomial
multiplier. -/
theorem samplingIdealizer_collapse {m : ℕ} {S : Set ℝ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ}
    (hlf : LocallyFiniteSamples S) (hsym : ∀ x, x ∈ S → -x ∈ S)
    (hsuper : SuperlinearSamples S) (h0 : (0 : ℝ) ∈ F)
    (hpres : PreservesSamplingIdeal m S F a) :
    ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → a h j = 0 := by
  intro h hhF j hj hcase
  rcases eq_or_ne h 0 with rfl | hh
  · have hj0 : j ≠ 0 := hcase.resolve_left (by simp)
    exact derivCoeff_eq_zero_of_infinite_samples hlf hpres h0
      (infinite_of_superlinearSamples hsuper) hj hj0
  · exact shiftCoeff_eq_zero_of_infinite_failure hlf hpres hhF
      (infinite_shiftFailure_of_superlinear hlf hsym hsuper hh) hj

/-- After the collapse the operator is exactly multiplication by its zero-shift, zero-order
polynomial coefficient. -/
theorem shiftWeylEval_eq_polynomial_multiplier {m : ℕ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ} (h0 : (0 : ℝ) ∈ F)
    (hcollapse : ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → a h j = 0)
    (φ : ℝ → ℂ) (x : ℝ) :
    shiftWeylEval m F a φ x = (a 0 0).eval (x : ℂ) * φ x := by
  classical
  rw [shiftWeylEval, Finset.sum_eq_single (0 : ℝ)]
  · rw [Finset.sum_eq_single 0]
    · rw [add_zero, iteratedDeriv_zero]
    · intro k hk hk0
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [hcollapse 0 h0 k hk' (Or.inr hk0), Polynomial.eval_zero, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) hnot
  · intro h' hh' hne
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k ≤ m := by
      have := Finset.mem_range.mp hk
      omega
    rw [hcollapse h' hh' k hk' (Or.inl hne), Polynomial.eval_zero, zero_mul]
  · intro hnot
    exact absurd h0 hnot

/-- Polynomial multiplication preserves every sampling ideal. -/
theorem preservesSamplingIdeal_polynomialMultiplier (m : ℕ) (S : Set ℝ) (p : Polynomial ℂ) :
    PreservesSamplingIdeal m S {0} (fun h j => if h = 0 ∧ j = 0 then p else 0) := by
  classical
  intro φ hφ γ hγ
  rw [shiftWeylEval, Finset.sum_singleton, Finset.sum_eq_single 0]
  · rw [add_zero, iteratedDeriv_zero, hφ γ hγ, mul_zero]
  · intro k _ hk0
    rw [if_neg (by simp [hk0]), Polynomial.eval_zero, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) hnot

/-! ## Symmetric multipliers and the canonical commutation obstruction -/

/-- A polynomial taking conjugation-invariant values on an infinite real set has real
coefficients. -/
theorem polynomial_conj_eq_of_infinite_real {p : Polynomial ℂ} {S : Set ℝ} (hS : S.Infinite)
    (hreal : ∀ γ ∈ S, (starRingEnd ℂ) (p.eval (γ : ℂ)) = p.eval (γ : ℂ)) :
    p.map (starRingEnd ℂ) = p := by
  have hzero : p.map (starRingEnd ℂ) - p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono (s := (fun γ : ℝ => (γ : ℂ)) '' S) ?_
      (hS.image (Complex.ofReal_injective.injOn))
    rintro _ ⟨γ, hγ, rfl⟩
    have hconj : (starRingEnd ℂ) ((γ : ℂ)) = (γ : ℂ) := Complex.conj_ofReal γ
    have hmap : (p.map (starRingEnd ℂ)).eval ((γ : ℂ))
        = (starRingEnd ℂ) (p.eval ((γ : ℂ))) := by
      conv_lhs => rw [← hconj]
      exact Polynomial.eval_map_apply (starRingEnd ℂ) ((γ : ℂ))
    show (p.map (starRingEnd ℂ) - p).eval ((γ : ℂ)) = 0
    rw [Polynomial.eval_sub, hmap, hreal γ hγ, sub_self]
  exact sub_eq_zero.mp hzero

/-- **No nonzero canonical commutation relation survives.**  Two polynomial multipliers commute on
the sampling quotient, so a scalar commutator on a nonempty sampling set is zero. -/
theorem ccr_scalar_eq_zero {p q : Polynomial ℂ} {lam : ℂ} {S : Set ℝ} (hS : S.Nonempty)
    (hccr : ∀ γ ∈ S, p.eval ((γ : ℂ)) * q.eval ((γ : ℂ))
      - q.eval ((γ : ℂ)) * p.eval ((γ : ℂ)) = lam) :
    lam = 0 := by
  obtain ⟨γ, hγ⟩ := hS
  have := hccr γ hγ
  rw [mul_comm, sub_self] at this
  exact this.symm

end

end RHTower
