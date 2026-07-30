/-
# The lattice field of the SPUR-R energy analysis (docs 29–31, tasks #138/#142)

The section-field electrostatic model (doc 27–29): charges at log-positions `t k`, the
field `Σ_k coth((x − t k)/2)`. Two facts drive the `s`-march (doc 29 step (b)) and hence
(S-mono):

* `cothField_strictAntiOn` — the field is STRICTLY DECREASING on any open interval free of
  poles. Consequence: the equilibrium `Σ coth = −d` in each gap is UNIQUE
  (`cothField_eq_unique`), and it moves monotonically when the field is shifted.
* `cothField_lt_of_swap_ge` — replacing an ahead-pole by a behind-pole shifts the field
  DOWN by more than `2` at every interior point (each `coth` term exceeds `1`,
  `one_lt_rcoth_of_pos`): the swap step of the march.

Everything is finite-sum `coth` algebra over `CothInfra`; no derivatives, no analysis
beyond `sinh` monotonicity.
-/
import GaloisForLFunctions.RHTower.CothInfra

namespace RHTower

open Real Set

/-- `coth` is strictly antitone on the negative axis (by oddness of `coth`). -/
theorem rcoth_strictAntiOn_neg : StrictAntiOn rcoth (Iio 0) := by
  intro x hx y hy hxy
  simp only [mem_Iio] at hx hy
  have h2 : -y < -x := by linarith
  have hb : (-x) ∈ Ioi (0:ℝ) := mem_Ioi.mpr (by linarith)
  have ha : (-y) ∈ Ioi (0:ℝ) := mem_Ioi.mpr (by linarith)
  have := rcoth_strictAntiOn_pos ha hb h2
  rw [rcoth_neg, rcoth_neg] at this
  linarith

/-- A single field term `x ↦ coth((x − p)/2)` is strictly antitone on any open interval
`(a,b)` that does not contain the pole `p`. -/
theorem cothTerm_strictAntiOn {p a b : ℝ} (hp : p ≤ a ∨ b ≤ p) :
    StrictAntiOn (fun x => rcoth ((x - p) / 2)) (Ioo a b) := by
  intro x hx y hy hxy
  simp only [mem_Ioo] at hx hy
  rcases hp with hpa | hbp
  · have hax : (0:ℝ) < (x - p) / 2 := by have := hx.1; linarith
    have hay : (0:ℝ) < (y - p) / 2 := by have := hy.1; linarith
    exact rcoth_strictAntiOn_pos (mem_Ioi.mpr hax) (mem_Ioi.mpr hay) (by linarith)
  · have hax : (x - p) / 2 < 0 := by have := hx.2; linarith
    have hay : (y - p) / 2 < 0 := by have := hy.2; linarith
    exact rcoth_strictAntiOn_neg (mem_Iio.mpr hax) (mem_Iio.mpr hay) (by linarith)

/-- The lattice field `Σ_k coth((x − t k)/2)`. -/
noncomputable def cothField {ι : Type*} (s : Finset ι) (t : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ s, rcoth ((x - t k) / 2)

/-- **Field monotonicity.** With a nonempty charge set none of whose poles lies in the open
gap `(a,b)`, the field is strictly decreasing on `(a,b)`. -/
theorem cothField_strictAntiOn {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hne : s.Nonempty) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) :
    StrictAntiOn (cothField s t) (Ioo a b) := by
  intro x hx y hy hxy
  simp only [cothField]
  exact Finset.sum_lt_sum_of_nonempty hne
    (fun k hk => cothTerm_strictAntiOn (hpoles k hk) hx hy hxy)

/-- **Uniqueness of the gap equilibrium.** Since the field is strictly decreasing on the
pole-free gap, it hits any level `c` at most once there. -/
theorem cothField_eq_unique {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b c : ℝ}
    (hne : s.Nonempty) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hxc : cothField s t x = c) (hyc : cothField s t y = c) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact absurd (hxc ▸ hyc ▸ cothField_strictAntiOn s t hne hpoles hx hy h) (by simp)
  · exact h
  · exact absurd (hyc ▸ hxc ▸ cothField_strictAntiOn s t hne hpoles hy hx h) (by simp)

/-- **The swap step bound.** At any interior point `x` of the gap, a behind-pole `p_b ≤ a`
and an ahead-pole `p_a ≥ b` each contribute a `coth`-term exceeding `1` in absolute value:
their combined signed contribution to the field, on removing `p_a` (ahead, negative term)
and adding `p_b` (behind, positive term), moves the field by more than `2`. Concretely both
`coth((x − p_b)/2) > 1` and `−coth((x − p_a)/2) > 1`. -/
theorem swap_terms_gt_one {p_b p_a a b x : ℝ} (hpb : p_b ≤ a) (hpa : b ≤ p_a)
    (hx : x ∈ Ioo a b) :
    1 < rcoth ((x - p_b) / 2) ∧ 1 < - rcoth ((x - p_a) / 2) := by
  simp only [mem_Ioo] at hx
  refine ⟨?_, ?_⟩
  · exact one_lt_rcoth_of_pos (by have := hx.1; linarith)
  · have hneg : (x - p_a) / 2 < 0 := by have := hx.2; linarith
    have : rcoth ((x - p_a) / 2) = - rcoth (-(x - p_a) / 2) := by
      rw [show -(x - p_a) / 2 = -((x - p_a)/2) by ring, rcoth_neg]; ring
    rw [this, neg_neg]
    exact one_lt_rcoth_of_pos (by linarith)

/-- `coth` is continuous at every nonzero point (denominator `sinh` nonvanishing there). -/
theorem rcoth_continuousAt {x : ℝ} (hx : x ≠ 0) : ContinuousAt rcoth x := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  exact (Real.continuous_cosh.continuousAt).div (Real.continuous_sinh.continuousAt) hs

/-- The lattice field is continuous on any pole-free open gap. -/
theorem cothField_continuousOn {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) :
    ContinuousOn (cothField s t) (Ioo a b) := by
  apply continuousOn_finsetSum
  intro k hk x hx
  simp only [mem_Ioo] at hx
  have hne : (x - t k) / 2 ≠ 0 := by
    rcases hpoles k hk with h | h
    · exact ne_of_gt (by have := hx.1; linarith)
    · exact ne_of_lt (by have := hx.2; linarith)
  have hca : ContinuousAt (fun y => rcoth ((y - t k) / 2)) x := by
    simp only [rcoth]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (Real.sinh_ne_zero.mpr hne)
  exact hca.continuousWithinAt

/-- **Existence of the gap equilibrium** (IVT). Given interior witnesses bracketing the
level `c` (which hold near the poles, where the field runs from `+∞` to `−∞`), the field
attains `c` in the gap; with `cothField_eq_unique` the equilibrium is unique. -/
theorem cothField_exists_equilibrium {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b c : ℝ}
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k)
    {xlo xhi : ℝ} (hlo : xlo ∈ Ioo a b) (hhi : xhi ∈ Ioo a b) (hxle : xlo ≤ xhi)
    (hchi : cothField s t xhi ≤ c) (hclo : c ≤ cothField s t xlo) :
    ∃ x ∈ Icc xlo xhi, cothField s t x = c := by
  have hsub : Icc xlo xhi ⊆ Ioo a b := by
    simp only [mem_Ioo] at hlo hhi
    exact Icc_subset_Ioo hlo.1 hhi.2
  have hcont : ContinuousOn (cothField s t) (Icc xlo xhi) :=
    (cothField_continuousOn s t hpoles).mono hsub
  have hmem : c ∈ Icc (cothField s t xhi) (cothField s t xlo) := ⟨hchi, hclo⟩
  obtain ⟨x, hx, hxc⟩ := intermediate_value_Icc' hxle hcont hmem
  exact ⟨x, hx, hxc⟩

/-- The reduced spectator energy `W(x) = ¼ Σ csch²((x − t_k)/2)` (doc 27–29). -/
noncomputable def spurLatticeEnergy {ι : Type*} (s : Finset ι) (t : ι → ℝ) (x : ℝ) : ℝ :=
  (1 / 4) * ∑ k ∈ s, (rcsch ((x - t k) / 2)) ^ 2

theorem spurLatticeEnergy_nonneg {ι : Type*} (s : Finset ι) (t : ι → ℝ) (x : ℝ) :
    0 ≤ spurLatticeEnergy s t x := by
  rw [spurLatticeEnergy]
  positivity

/-- **The exact field–energy identity `field′ = −2·W`** (doc 28 §5c, `σ̇₁ = −2W̃`): on a
pole-free gap the lattice field's slope is minus twice the reduced energy. This converts
(S-mono) `W(t*_{i+1}) > W(t*_i)` into a slope statement about the field at its equilibria. -/
theorem cothField_hasDerivAt {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b x : ℝ}
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) (hx : x ∈ Ioo a b) :
    HasDerivAt (cothField s t) (-2 * spurLatticeEnergy s t x) x := by
  simp only [mem_Ioo] at hx
  have hterm : ∀ k ∈ s, HasDerivAt (fun y => rcoth ((y - t k) / 2))
      (-(1 / 2) * (rcsch ((x - t k) / 2)) ^ 2) x := by
    intro k hk
    have hne : (x - t k) / 2 ≠ 0 := by
      rcases hpoles k hk with h | h
      · exact ne_of_gt (by linarith)
      · exact ne_of_lt (by linarith)
    have hin : HasDerivAt (fun y : ℝ => (y - t k) / 2) (1 / 2) x := by
      simpa using ((hasDerivAt_id x).sub_const (t k)).div_const 2
    have := (rcoth_hasDerivAt hne).comp x hin
    simpa only [Function.comp_apply] using! this.congr_deriv (by ring)
  have hsum := HasDerivAt.fun_sum (fun k hk => hterm k hk)
  have hval : (-2 : ℝ) * spurLatticeEnergy s t x
      = ∑ k ∈ s, -(1 / 2) * (rcsch ((x - t k) / 2)) ^ 2 := by
    rw [spurLatticeEnergy, ← mul_assoc, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k hk => by ring)
  rw [hval]
  exact hsum

/-- **The energy slope `W′ = −¼ Σ φ`** (`φ = rphi = csch²·coth`), on a pole-free gap. With
`cothField_hasDerivAt` (`field′ = −2W`) this is the second derivative of the field:
`field″ = −2W′ = ½ Σ φ`. -/
theorem spurLatticeEnergy_hasDerivAt {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b x : ℝ}
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) (hx : x ∈ Ioo a b) :
    HasDerivAt (spurLatticeEnergy s t) (-(1 / 4) * ∑ k ∈ s, rphi ((x - t k) / 2)) x := by
  simp only [mem_Ioo] at hx
  have hterm : ∀ k ∈ s, HasDerivAt (fun y => (rcsch ((y - t k) / 2)) ^ 2)
      (-rphi ((x - t k) / 2)) x := by
    intro k hk
    have hne : (x - t k) / 2 ≠ 0 := by
      rcases hpoles k hk with h | h
      · exact ne_of_gt (by linarith)
      · exact ne_of_lt (by linarith)
    have hin : HasDerivAt (fun y : ℝ => (y - t k) / 2) (1 / 2) x := by
      simpa using ((hasDerivAt_id x).sub_const (t k)).div_const 2
    have hcmp := (rcsch_sq_hasDerivAt hne).comp x hin
    simpa only [Function.comp_apply] using! hcmp.congr_deriv (by ring)
  have hsum := HasDerivAt.fun_sum (fun k hk => hterm k hk)
  have hval : (-(1 / 4 : ℝ)) * ∑ k ∈ s, rphi ((x - t k) / 2)
      = (1 / 4 : ℝ) * ∑ k ∈ s, -rphi ((x - t k) / 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k hk => by ring)
  rw [hval]
  exact hsum.const_mul (1 / 4)

/-- **Field second derivative `field″ = ½ Σ φ`** on a pole-free gap: differentiating
`field′ = −2W` (`cothField_hasDerivAt`) via `W′ = −¼Σφ` (`spurLatticeEnergy_hasDerivAt`). Its sign
is set by the balance of behind (`φ > 0`) and ahead (`φ < 0`) charges — the field is convex
where behind-dominated, concave where ahead-dominated. -/
theorem cothField_secondDeriv {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b x : ℝ}
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => -2 * spurLatticeEnergy s t y)
      ((1 / 2) * ∑ k ∈ s, rphi ((x - t k) / 2)) x := by
  have h := (spurLatticeEnergy_hasDerivAt s t hpoles hx).const_mul (-2 : ℝ)
  exact h.congr_deriv (by ring)

/-- **The march mechanism (pure monotonicity).** If two strictly-decreasing fields `F, G`
on a common gap have equilibria `xF, xG` at the same level `c`, and `G` sits strictly below
`F` at `xF` (the swap depresses the field), then the `G`-equilibrium lies strictly to the
LEFT: `xG < xF`. This is the doc-29 step-(b) march `s_{i+1} < s_i`, in equilibrium form,
independent of the specific field. -/
theorem equilibrium_lt_of_field_lt {F G : ℝ → ℝ} {a b c xF xG : ℝ}
    (hG : StrictAntiOn G (Ioo a b))
    (hxF : xF ∈ Ioo a b) (hxG : xG ∈ Ioo a b)
    (hFc : F xF = c) (hGc : G xG = c) (hlt : G xF < F xF) : xG < xF := by
  have hkey : G xF < G xG := by rw [hGc, ← hFc]; exact hlt
  by_contra h
  rw [not_lt] at h
  rcases eq_or_lt_of_le h with h1 | h1
  · rw [h1] at hkey; exact lt_irrefl _ hkey
  · exact absurd (hG hxF hxG h1) (by linarith)

/-- **The swap raises the field by more than 2.** Passing from gap `i` to gap `i+1`
converts the near-ahead pole into a near-behind pole (doc 29 step (b)); at any interior
point the field gains `coth((x−p_b)/2) − coth((x−p_a)/2) > 2` (both `swap_terms_gt_one`). -/
theorem swap_field_gt {fP fQ : ℝ → ℝ} {p_b p_a a b x : ℝ}
    (hpb : p_b ≤ a) (hpa : b ≤ p_a) (hx : x ∈ Ioo a b)
    (hdiff : fQ x = fP x + rcoth ((x - p_b) / 2) - rcoth ((x - p_a) / 2)) :
    fP x + 2 < fQ x := by
  obtain ⟨h1, h2⟩ := swap_terms_gt_one hpb hpa hx
  rw [hdiff]; linarith

/-- **The swap moves the equilibrium right** (mirror of `equilibrium_lt_of_field_lt`). If
`G` sits strictly ABOVE `F` at `F`'s equilibrium, then `G`'s equilibrium is strictly to the
right — the s-march `s_{i+1} < s_i` (the equilibrium tightens toward the ahead pole). -/
theorem equilibrium_gt_of_field_gt {F G : ℝ → ℝ} {a b c xF xG : ℝ}
    (hG : StrictAntiOn G (Ioo a b))
    (hxF : xF ∈ Ioo a b) (hxG : xG ∈ Ioo a b)
    (hFc : F xF = c) (hGc : G xG = c) (hgt : F xF < G xF) : xF < xG := by
  have hkey : G xG < G xF := by rw [hGc, ← hFc]; exact hgt
  by_contra h
  rw [not_lt] at h
  rcases eq_or_lt_of_le h with h1 | h1
  · rw [h1] at hkey; exact lt_irrefl _ hkey
  · exact absurd (hG hxG hxF h1) (by linarith)

/-- **Near-dominates-far** (the doc-29(c) / (χ2) engine). When the near-ahead distance `s`
is below the half-gap (`2s < δ`), the near spectator weight `φ(s/2)` strictly exceeds the
far one `φ((δ−s)/2)` — the term that makes `dW/ds < 0`, hence `W` grows as the equilibrium
tightens toward the ahead pole. Immediate from `rphi_strictAntiOn_pos`. -/
theorem rphi_near_gt_far {s δ : ℝ} (hs : 0 < s) (hsδ : 2 * s < δ) :
    rphi ((δ - s) / 2) < rphi (s / 2) := by
  have h1 : (0 : ℝ) < s / 2 := by linarith
  have h2 : s / 2 < (δ - s) / 2 := by linarith
  exact rphi_strictAntiOn_pos (mem_Ioi.mpr h1) (mem_Ioi.mpr (by linarith)) h2

/-- **Paired-difference** (the `m`-th summand of `dW/ds`). For the near-ahead distance `s`
below the half-gap, the `m`-th ahead spectator `φ((s+mδ)/2)` strictly exceeds the `m`-th
behind spectator `φ((δ−s+mδ)/2)` — every paired term of the doc-29(c) sum favors `dW/ds<0`,
so once the far-behind surplus (the `N>M` overhang) is controlled by its exponential tail,
`W` grows along the march. -/
theorem rphi_pair_gt {s δ w : ℝ} (hs : 0 < s) (hsδ : 2 * s < δ) (hw : 0 ≤ w) :
    rphi ((δ - s + w) / 2) < rphi ((s + w) / 2) := by
  have h1 : (0 : ℝ) < (s + w) / 2 := by linarith
  have h2 : (s + w) / 2 < (δ - s + w) / 2 := by linarith
  exact rphi_strictAntiOn_pos (mem_Ioi.mpr h1) (mem_Ioi.mpr (by linarith)) h2

/-- **The paired sum is positive** (the unconditional half of `dW/ds<0`): summing the
paired differences over any finite index set, `Σ φ((s+mδ)/2) > Σ φ((δ−s+mδ)/2)` when the
index set is nonempty and `2s<δ`. This is `dW/ds<0` exactly when there is no far-behind
overhang (`M ≥ N`, the inner/mid range); the outer range adds the exponential tail. -/
theorem rphi_paired_sum_gt {ι : Type*} (u : Finset ι) (w : ι → ℝ) {s δ : ℝ}
    (hne : u.Nonempty) (hs : 0 < s) (hsδ : 2 * s < δ) (hw : ∀ i ∈ u, 0 ≤ w i) :
    ∑ i ∈ u, rphi ((δ - s + w i) / 2) < ∑ i ∈ u, rphi ((s + w i) / 2) :=
  Finset.sum_lt_sum_of_nonempty hne (fun i hi => rphi_pair_gt hs hsδ (hw i hi))

/-- The `s`-parametrized constant-δ lattice energy `W(s) = ¼[Σ_{m<M} csch²((s+mδ)/2) +
Σ_{n<N} csch²((δ−s+nδ)/2)]`: the equilibrium slid within its gap, near-ahead distance `s`,
`M` charges ahead and `N` behind at spacing `δ`. -/
noncomputable def latticeEnergyS (δ : ℝ) (M N : ℕ) (s : ℝ) : ℝ :=
  (1 / 4) * ((∑ m ∈ Finset.range M, (rcsch ((s + m * δ) / 2)) ^ 2)
    + ∑ n ∈ Finset.range N, (rcsch ((δ - s + n * δ) / 2)) ^ 2)

/-- **`dW/ds = ¼[Σ_{n} φ((δ−s+nδ)/2) − Σ_{m} φ((s+mδ)/2)]`.** The ahead charges pull the
energy down as `s` shrinks (`−φ`), the behind charges push it up (`+φ`); the near-ahead pole
dominates. Valid on `0 < s < δ` (all arguments positive). -/
theorem latticeEnergyS_hasDerivAt {δ : ℝ} {M N : ℕ} {s : ℝ} (hδ : 0 < δ)
    (hs0 : 0 < s) (hsδ : s < δ) :
    HasDerivAt (latticeEnergyS δ M N)
      ((1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - s + n * δ) / 2))
        - ∑ m ∈ Finset.range M, rphi ((s + m * δ) / 2))) s := by
  have hahead : ∀ m ∈ Finset.range M, HasDerivAt (fun y => (rcsch ((y + m * δ) / 2)) ^ 2)
      (-rphi ((s + m * δ) / 2)) s := by
    intro m _
    have hne : (s + m * δ) / 2 ≠ 0 := by positivity
    have hin : HasDerivAt (fun y : ℝ => (y + m * δ) / 2) (1 / 2) s := by
      simpa using ((hasDerivAt_id s).add_const (m * δ)).div_const 2
    have := (rcsch_sq_hasDerivAt hne).comp s hin
    simpa only [Function.comp_apply] using! this.congr_deriv (by ring)
  have hbehind : ∀ n ∈ Finset.range N, HasDerivAt (fun y => (rcsch ((δ - y + n * δ) / 2)) ^ 2)
      (rphi ((δ - s + n * δ) / 2)) s := by
    intro n _
    have hpos : (0 : ℝ) < (δ - s + n * δ) / 2 := by positivity
    have hne : (δ - s + n * δ) / 2 ≠ 0 := ne_of_gt hpos
    have hin : HasDerivAt (fun y : ℝ => (δ - y + n * δ) / 2) (-1 / 2) s := by
      have h0 : HasDerivAt (fun y : ℝ => δ - y + n * δ) (-1) s := by
        simpa using ((hasDerivAt_id s).const_sub δ).add_const (n * δ)
      simpa using h0.div_const 2
    have := (rcsch_sq_hasDerivAt hne).comp s hin
    simpa only [Function.comp_apply] using! this.congr_deriv (by ring)
  have hA := HasDerivAt.fun_sum (fun m hm => hahead m hm)
  have hB := HasDerivAt.fun_sum (fun n hn => hbehind n hn)
  have hsum := (hA.add hB).const_mul (1 / 4 : ℝ)
  have hcoef :
      (1 / 4 : ℝ) * ((∑ m ∈ Finset.range M, -rphi ((s + m * δ) / 2)) +
        ∑ n ∈ Finset.range N, rphi ((δ - s + n * δ) / 2)) =
        (1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - s + n * δ) / 2)) -
          ∑ m ∈ Finset.range M, rphi ((s + m * δ) / 2)) := by
    rw [Finset.sum_neg_distrib]
    ring
  simpa only [latticeEnergyS, Pi.add_apply] using! hsum.congr_deriv hcoef

/-- **`dW/ds < 0` when `M ≥ N ≥ 1`** — the unconditional (no far-behind overhang) case: the
ahead spectator sum strictly exceeds the behind one (paired sum + the extra ahead charges),
so the energy strictly decreases as the equilibrium slides toward the ahead pole. -/
theorem latticeEnergyS_deriv_neg {δ : ℝ} {M N : ℕ} {s : ℝ}
    (hs0 : 0 < s) (hsδ : 2 * s < δ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - s + n * δ) / 2))
      - ∑ m ∈ Finset.range M, rphi ((s + m * δ) / 2)) < 0 := by
  have hδ : 0 < δ := by linarith
  have hpair : (∑ n ∈ Finset.range N, rphi ((δ - s + (n : ℝ) * δ) / 2))
      < ∑ n ∈ Finset.range N, rphi ((s + (n : ℝ) * δ) / 2) :=
    rphi_paired_sum_gt (Finset.range N) (fun n => (n : ℝ) * δ)
      (Finset.nonempty_range_iff.mpr (by omega)) hs0 hsδ (fun n _ => by positivity)
  have hss : Finset.range N ⊆ Finset.range M := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNM)
  have hsub : (∑ n ∈ Finset.range N, rphi ((s + (n : ℝ) * δ) / 2))
      ≤ ∑ m ∈ Finset.range M, rphi ((s + (m : ℝ) * δ) / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hss
      (fun m _ _ => le_of_lt (rphi_pos_of_pos (by positivity)))
  have hlt := lt_of_lt_of_le hpair hsub
  linarith

/-- **`dW/ds < 0` in the outer range `N > M`**, reduced to the domination hypothesis: the
far-behind overhang `Σ_{M≤n<N} φ((δ−s+nδ)/2)` is beaten by the paired surplus
`Σ_{m<M} φ((s+mδ)/2) − Σ_{n<M} φ((δ−s+nδ)/2)`. The overhang is bounded above by the geometric
tail (`rphi_geom_tail_le`), the surplus below by the near cubic term (`rphi_ge_cubic` +
`rphi_near_gt_far`) — so `hdom` holds once `s` is small relative to the gap, closing the
outer range. -/
theorem latticeEnergyS_deriv_neg_outer {δ : ℝ} {M N : ℕ} {s : ℝ} (hMN : M ≤ N)
    (hdom : ∑ n ∈ Finset.Ico M N, rphi ((δ - s + (n : ℝ) * δ) / 2)
      < (∑ m ∈ Finset.range M, rphi ((s + (m : ℝ) * δ) / 2))
        - ∑ n ∈ Finset.range M, rphi ((δ - s + (n : ℝ) * δ) / 2)) :
    (1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - s + (n : ℝ) * δ) / 2))
      - ∑ m ∈ Finset.range M, rphi ((s + (m : ℝ) * δ) / 2)) < 0 := by
  have hsplit : (∑ n ∈ Finset.range M, rphi ((δ - s + (n : ℝ) * δ) / 2))
      + ∑ n ∈ Finset.Ico M N, rphi ((δ - s + (n : ℝ) * δ) / 2)
      = ∑ n ∈ Finset.range N, rphi ((δ - s + (n : ℝ) * δ) / 2) :=
    Finset.sum_range_add_sum_Ico _ hMN
  linarith [hsplit, hdom]

/-- **Closed-form overhang bound.** The far-behind overhang `Σ_{M≤n<N} φ((δ−s+nδ)/2)` is
below the geometric closed form `64·e^{−(δ−s+Mδ)}/(1−e^{−δ})` (reindex `n=M+k`, then
`rphi_geom_tail_le` with base `(δ−s+Mδ)/2 ≥ 1` and step `δ/2`). With this, `hnear` becomes a
pure scalar inequality — no sums. -/
theorem overhang_le_geom {δ s : ℝ} {M N : ℕ} (hδ : 0 < δ)
    (hbase : 1 ≤ (δ - s + (M : ℝ) * δ) / 2) :
    ∑ n ∈ Finset.Ico M N, rphi ((δ - s + (n : ℝ) * δ) / 2)
      ≤ 64 * Real.exp (-(δ - s + (M : ℝ) * δ)) / (1 - Real.exp (-δ)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hreidx : ∀ k ∈ Finset.range (N - M),
      rphi ((δ - s + ((M + k : ℕ) : ℝ) * δ) / 2)
        = rphi ((δ - s + (M : ℝ) * δ) / 2 + (k : ℝ) * (δ / 2)) := by
    intro k _
    congr 1; push_cast; ring
  rw [Finset.sum_congr rfl hreidx]
  have hgeom := rphi_geom_tail_le hbase (by linarith : (0 : ℝ) < δ / 2) (N - M)
  have he1 : (-2 : ℝ) * ((δ - s + (M : ℝ) * δ) / 2) = -(δ - s + (M : ℝ) * δ) := by ring
  have he2 : (-2 : ℝ) * (δ / 2) = -δ := by ring
  rw [he1, he2] at hgeom
  exact hgeom

/-- **Outer range reduced to the near margin.** Since the paired surplus dominates its `m=0`
term (all paired differences are positive, `rphi_pair_gt`), `dW/ds<0` for `N>M` follows once
the far-behind overhang is below the near margin `φ(s/2) − φ((δ−s)/2)` — a single scalar
inequality, with the overhang bounded by `rphi_geom_tail_le` and the margin below by
`rphi_ge_cubic`. This is the outer-range analogue of `latticeEnergyS_deriv_neg`. -/
theorem latticeEnergyS_deriv_neg_outer_of_near {δ : ℝ} {M N : ℕ} {s : ℝ}
    (hs0 : 0 < s) (hsδ : 2 * s < δ) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hnear : ∑ n ∈ Finset.Ico M N, rphi ((δ - s + (n : ℝ) * δ) / 2)
      < rphi (s / 2) - rphi ((δ - s) / 2)) :
    (1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - s + (n : ℝ) * δ) / 2))
      - ∑ m ∈ Finset.range M, rphi ((s + (m : ℝ) * δ) / 2)) < 0 := by
  apply latticeEnergyS_deriv_neg_outer hMN
  have hsurplus : rphi (s / 2) - rphi ((δ - s) / 2)
      ≤ (∑ m ∈ Finset.range M, rphi ((s + (m : ℝ) * δ) / 2))
        - ∑ n ∈ Finset.range M, rphi ((δ - s + (n : ℝ) * δ) / 2) := by
    rw [← Finset.sum_sub_distrib]
    have h0mem : (0 : ℕ) ∈ Finset.range M := Finset.mem_range.mpr (by omega)
    have hterms : ∀ m ∈ Finset.range M,
        (0 : ℝ) ≤ rphi ((s + (m : ℝ) * δ) / 2) - rphi ((δ - s + (m : ℝ) * δ) / 2) := by
      intro m _
      have := rphi_pair_gt hs0 hsδ
        (mul_nonneg (Nat.cast_nonneg m) (by linarith : (0 : ℝ) ≤ δ))
      linarith
    have hsingle := Finset.single_le_sum hterms h0mem
    simpa using hsingle
  linarith [hnear, hsurplus]

/-- **Outer-range `dW/ds < 0`, reduced to a single explicit scalar inequality.** Combining the
banked bounds — overhang ≤ geometric closed form (`overhang_le_geom`), near term ≥ cubic
(`rphi_ge_cubic`, `1/(4(s/2)³)=2/s³`), far term ≤ exponential (`rphi_le_exp`) — the outer
range closes provided `geometric-overhang + 64e^{−(δ−s)} < 2/s³`. That holds for `s` small
(the cubic `2/s³ → ∞` swamps the bounded exponential terms), closing the constant-δ lattice
(S-mono) in the outer range with NO remaining sums — only calculus in `(s, δ, M)`. -/
theorem latticeEnergyS_deriv_neg_outer_scalar {δ : ℝ} {M N : ℕ} {s : ℝ}
    (hs0 : 0 < s) (hs2 : s ≤ 2) (hsδ : 2 * s < δ) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hbase : 1 ≤ (δ - s + (M : ℝ) * δ) / 2) (hfar : 1 ≤ (δ - s) / 2)
    (hscalar : 64 * Real.exp (-(δ - s + (M : ℝ) * δ)) / (1 - Real.exp (-δ))
        + 64 * Real.exp (-(δ - s)) < 2 / s ^ 3) :
    (1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - s + (n : ℝ) * δ) / 2))
      - ∑ m ∈ Finset.range M, rphi ((s + (m : ℝ) * δ) / 2)) < 0 := by
  have hδ : 0 < δ := by linarith
  apply latticeEnergyS_deriv_neg_outer_of_near hs0 hsδ hM hMN
  have hoh := overhang_le_geom (N := N) hδ hbase
  have hcub : (2 : ℝ) / s ^ 3 ≤ rphi (s / 2) := by
    have h := rphi_ge_cubic (by linarith : 0 < s / 2) (by linarith : s / 2 ≤ 1)
    have hid : (1 : ℝ) / (4 * (s / 2) ^ 3) = 2 / s ^ 3 := by field_simp; ring
    rwa [hid] at h
  have hexp : rphi ((δ - s) / 2) ≤ 64 * Real.exp (-(δ - s)) := by
    have h := rphi_le_exp hfar
    rwa [show (-2 : ℝ) * ((δ - s) / 2) = -(δ - s) from by ring] at h
  linarith [hoh, hcub, hexp, hscalar]

/-- The outer-range scalar LHS is bounded by the δ-only constant
`C(δ) = 64 e^{−δ/2}(1/(1−e^{−δ}) + 1)` (since `δ−s ≥ δ/2` on `2s<δ`, and `Mδ ≥ 0`). -/
theorem scalar_lhs_le {δ s : ℝ} (M : ℕ) (hs0 : 0 < s) (hsδ : 2 * s < δ) :
    64 * Real.exp (-(δ - s + (M : ℝ) * δ)) / (1 - Real.exp (-δ)) + 64 * Real.exp (-(δ - s))
      ≤ 64 * Real.exp (-δ / 2) / (1 - Real.exp (-δ)) + 64 * Real.exp (-δ / 2) := by
  have hδ : 0 < δ := by linarith
  have hden : (0 : ℝ) < 1 - Real.exp (-δ) := by
    have : Real.exp (-δ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have he1 : Real.exp (-(δ - s + (M : ℝ) * δ)) ≤ Real.exp (-δ / 2) := by
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ (M : ℝ) * δ := mul_nonneg (Nat.cast_nonneg M) hδ.le
    linarith
  have he2 : Real.exp (-(δ - s)) ≤ Real.exp (-δ / 2) := by
    apply Real.exp_le_exp.mpr; linarith
  gcongr

/-- **Outer-range `dW/ds < 0` under an explicit s-independent smallness.** Bounding the scalar
LHS by `C(δ)` (`scalar_lhs_le`), the outer range closes once `C(δ) < 2/s³` — a clean condition
with the constant depending on `δ` alone, and `s³` the only place `s` enters. Holds for every
`s ≤ (2/C(δ))^{1/3}`: the outer range of the constant-δ lattice (S-mono), Lean-closed. -/
theorem latticeEnergyS_deriv_neg_outer_small {δ : ℝ} {M N : ℕ} {s : ℝ}
    (hs0 : 0 < s) (hs2 : s ≤ 2) (hsδ : 2 * s < δ) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hbase : 1 ≤ (δ - s + (M : ℝ) * δ) / 2) (hfar : 1 ≤ (δ - s) / 2)
    (hsmall : 64 * Real.exp (-δ / 2) / (1 - Real.exp (-δ)) + 64 * Real.exp (-δ / 2)
        < 2 / s ^ 3) :
    (1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - s + (n : ℝ) * δ) / 2))
      - ∑ m ∈ Finset.range M, rphi ((s + (m : ℝ) * δ) / 2)) < 0 :=
  latticeEnergyS_deriv_neg_outer_scalar hs0 hs2 hsδ hM hMN hbase hfar
    (lt_of_le_of_lt (scalar_lhs_le M hs0 hsδ) hsmall)

/-- **(S-mono) on the constant-δ lattice, no-overhang range.** For `1 ≤ N ≤ M`, the reduced
energy `W(s)` is STRICTLY DECREASING in the near-ahead distance `s ∈ (0, δ/2)`. So as the
march tightens the equilibrium toward the ahead pole (`s` shrinks, `equilibrium_gt_of_field_gt`),
`W` strictly increases — the reader-exactness monotonicity `S_{i+1} > S_i`, unconditional
wherever the ahead charges are at least as numerous as the behind ones. -/
theorem latticeEnergyS_strictAntiOn {δ : ℝ} {M N : ℕ} (hδ : 0 < δ) (hN : 1 ≤ N)
    (hNM : N ≤ M) : StrictAntiOn (latticeEnergyS δ M N) (Ioo 0 (δ / 2)) := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (δ / 2), HasDerivAt (latticeEnergyS δ M N)
      ((1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - x + n * δ) / 2))
        - ∑ m ∈ Finset.range M, rphi ((x + m * δ) / 2))) x := by
    intro x hx
    simp only [mem_Ioo] at hx
    exact latticeEnergyS_hasDerivAt hδ hx.1 (by linarith [hx.2])
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (δ / 2))
  · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo, mem_Ioo] at hx
    rw [(hderiv x (mem_Ioo.mpr hx)).deriv]
    exact latticeEnergyS_deriv_neg hx.1 (by linarith [hx.2]) hN hNM

/-- **(S-mono) on the constant-δ lattice, OUTER range**, as `StrictAntiOn` on a small-`s`
interval `(0, r)`. On that interval the regime conditions (`hbase`, `hfar`, the scalar
smallness `hsmall`) hold, so `latticeEnergyS_deriv_neg_outer_small` gives `dW/ds<0` pointwise
and `strictAntiOn_of_deriv_neg` integrates it. Together with `latticeEnergyS_strictAntiOn`
(no-overhang) this is (S-mono) for both charge regimes. -/
theorem latticeEnergyS_strictAntiOn_outer {δ : ℝ} {M N : ℕ} {r : ℝ}
    (hM : 1 ≤ M) (hMN : M ≤ N) (hr : 0 < r) (hr2 : r ≤ 2) (hrδ : 2 * r < δ)
    (hbase : ∀ x ∈ Ioo (0 : ℝ) r, 1 ≤ (δ - x + (M : ℝ) * δ) / 2)
    (hfar : ∀ x ∈ Ioo (0 : ℝ) r, 1 ≤ (δ - x) / 2)
    (hsmall : ∀ x ∈ Ioo (0 : ℝ) r,
      64 * Real.exp (-δ / 2) / (1 - Real.exp (-δ)) + 64 * Real.exp (-δ / 2) < 2 / x ^ 3) :
    StrictAntiOn (latticeEnergyS δ M N) (Ioo 0 r) := by
  have hδ : 0 < δ := by linarith
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) r, HasDerivAt (latticeEnergyS δ M N)
      ((1 / 4) * ((∑ n ∈ Finset.range N, rphi ((δ - x + (n : ℝ) * δ) / 2))
        - ∑ m ∈ Finset.range M, rphi ((x + (m : ℝ) * δ) / 2))) x := by
    intro x hx
    simp only [mem_Ioo] at hx
    exact latticeEnergyS_hasDerivAt hδ hx.1 (by linarith [hx.2])
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 r)
  · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo, mem_Ioo] at hx
    rw [(hderiv x (mem_Ioo.mpr hx)).deriv]
    exact latticeEnergyS_deriv_neg_outer_small hx.1 (by linarith [hx.2]) (by linarith [hx.2])
      hM hMN (hbase x (mem_Ioo.mpr hx)) (hfar x (mem_Ioo.mpr hx)) (hsmall x (mem_Ioo.mpr hx))

/-- The lattice reduced energy is an **antitone dressing** on the s-domain — the exact form
`SpurSMono.ampReaderInput_of_smono_dressing_ge` consumes to package `AMPReaderInput`: the
`s ↦ W(s)` map is the S-to-margin dressing, and (S-mono) is its (anti)monotonicity. -/
theorem latticeEnergyS_antitoneOn {δ : ℝ} {M N : ℕ} (hδ : 0 < δ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    AntitoneOn (latticeEnergyS δ M N) (Ioo 0 (δ / 2)) :=
  (latticeEnergyS_strictAntiOn hδ hN hNM).antitoneOn

/-- **(S-mono), sequence form (no-overhang range).** Given a strictly DECREASING sequence of
near-ahead distances `s i ∈ (0, δ/2)` — exactly what the s-march produces
(`equilibrium_gt_of_field_gt`: each step tightens the equilibrium toward the ahead pole) —
the reduced-energy sequence `W(s i)` is strictly INCREASING. This is the reader-exactness
monotonicity `S_{i+1} > S_i` in abstract sequence form, unconditional for `1 ≤ N ≤ M`. -/
theorem latticeEnergyS_seq_strictMono {δ : ℝ} {M N : ℕ} (hδ : 0 < δ) (hN : 1 ≤ N)
    (hNM : N ≤ M) {s : ℕ → ℝ} (hs_mem : ∀ i, s i ∈ Ioo 0 (δ / 2))
    (hs_anti : StrictAnti s) : StrictMono (fun i => latticeEnergyS δ M N (s i)) :=
  fun _ _ hij =>
    latticeEnergyS_strictAntiOn hδ hN hNM (hs_mem _) (hs_mem _) (hs_anti hij)

end RHTower
