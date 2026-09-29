/-
# Local branches of the Böttcher coordinate and propagation of relations

On the basin `Ω_c = K_cᶜ` a *local branch* of the Böttcher coordinate on an open set `O` is a
holomorphic `g` with `g' = ω·g`, where `ω = d log φ_c` is single-valued on `Ω_c`.

* **Existence.**  On a disc in `Ω_c` every value is taken by a branch: `g = v·e^Φ` for a primitive
  `Φ` of `ω`.
* **Uniqueness.**  Two branches on a connected open set agreeing at one point agree everywhere:
  `(g - g')·e^{-Φ}` has zero derivative near the point, and the identity theorem spreads the
  agreement.
* **Propagation.**  Let `R(y, X)` and `S(y, X)` be relations whose substitutions `y ↦ R(y, g y)` are
  analytic for every holomorphic `g`.  If some disc in a connected open `D ⊆ Ω_c` carries a branch
  `g` with `R(·, g) ≡ 0` and `S(·, g) ≢ 0`, then so does a disc around every point of `D`.  The set
  of such points is open, and it is closed in `D`: near a limit point `z` a good disc overlaps the
  disc around `z` in a convex set, where the branch on the disc around `z` with the same value
  agrees with the good branch, and the identity theorem transfers both relations.

This continues an algebraic relation between a multivalued Böttcher coordinate and single-valued
analytic data from the far field to any point of a connected region, with no paths.
-/
import GaloisForLFunctions.Bottcher.BottcherContinuation

open Complex Set Filter Topology Metric

namespace Bottcher

/-- `g` is a local branch of the Böttcher coordinate of `c` on `O`: `g' = ω·g` there. -/
def IsBasinBranch (c : ℂ) (O : Set ℂ) (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g O ∧ ∀ z ∈ O, deriv g z = greenLogDeriv c z * g z

theorem IsBasinBranch.mono {c : ℂ} {O O' : Set ℂ} {g : ℂ → ℂ} (hg : IsBasinBranch c O g)
    (h : O' ⊆ O) : IsBasinBranch c O' g :=
  ⟨hg.1.mono h, fun z hz => hg.2 z (h hz)⟩

/-- `φ_c` is a branch on every subset of the escape region. -/
theorem isBasinBranch_bottcherCoord {c : ℂ} {O : Set ℂ} (hO : O ⊆ escapeOpen c) :
    IsBasinBranch c O (bottcherCoord c) :=
  ⟨(differentiableOn_bottcherCoord_escape c).mono hO,
    fun _ hz => deriv_bottcherCoord_eq_greenLogDeriv_mul (hO hz)⟩

/-- **Branches on discs take every value at every point.** -/
theorem exists_isBasinBranch_ball {c z₀ : ℂ} {r : ℝ} (hball : ball z₀ r ⊆ (filledJulia c)ᶜ)
    (y₀ v : ℂ) : ∃ g, IsBasinBranch c (ball z₀ r) g ∧ g y₀ = v := by
  obtain ⟨Φ, hΦ0, hΦ⟩ :=
    ((differentiableOn_greenLogDeriv c).mono hball).isExactOn_ball.with_val_at y₀ 0
  refine ⟨fun z => v * Complex.exp (Φ z),
    ⟨fun z hz => ((hΦ z hz).differentiableAt.cexp.const_mul v).differentiableWithinAt,
      fun z hz => ?_⟩, by simp [hΦ0]⟩
  rw [((hΦ z hz).cexp.const_mul v).deriv]
  ring

/-- **Branches are determined by one value** on a connected open subset of the basin. -/
theorem IsBasinBranch.eqOn_of_preconnected {c : ℂ} {O : Set ℂ} {g g' : ℂ → ℂ} (hOo : IsOpen O)
    (hOc : IsPreconnected O) (hOK : O ⊆ (filledJulia c)ᶜ) (hg : IsBasinBranch c O g)
    (hg' : IsBasinBranch c O g') {z₀ : ℂ} (hz₀ : z₀ ∈ O) (heq : g z₀ = g' z₀) :
    EqOn g g' O := by
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOo z₀ hz₀
  obtain ⟨Φ, -, hΦ⟩ :=
    ((differentiableOn_greenLogDeriv c).mono (hrO.trans hOK)).isExactOn_ball.with_val_at z₀ 0
  set k : ℂ → ℂ := fun z => (g z - g' z) * Complex.exp (-Φ z) with hkdef
  have hk : ∀ z ∈ ball z₀ r, HasDerivAt k 0 z := by
    intro z hz
    have hzO := hrO hz
    have hgd : HasDerivAt g (greenLogDeriv c z * g z) z := by
      rw [← hg.2 z hzO]; exact (hg.1.differentiableAt (hOo.mem_nhds hzO)).hasDerivAt
    have hg'd : HasDerivAt g' (greenLogDeriv c z * g' z) z := by
      rw [← hg'.2 z hzO]; exact (hg'.1.differentiableAt (hOo.mem_nhds hzO)).hasDerivAt
    exact ((hgd.sub hg'd).mul (hΦ z hz).neg.cexp).congr_deriv
      (by simp only [Pi.sub_apply, Pi.neg_apply]; ring)
  have hconst : ∀ z ∈ ball z₀ r, k z = k z₀ := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
      (fun t ht => (hk t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hk t ht).deriv) hz (mem_ball_self hr)
  have hev : (fun z => g z - g' z) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    have h1 := hconst z hz
    simp only [hkdef, heq, sub_self, zero_mul, mul_eq_zero, Complex.exp_ne_zero, or_false] at h1
    exact h1
  have han : AnalyticOnNhd ℂ (fun z => g z - g' z) O := (hg.1.sub hg'.1).analyticOnNhd hOo
  intro z hz
  exact sub_eq_zero.mp (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hOc hz₀ hev hz)

/-- An analytic function not identically zero on a connected open set is not identically zero on
any nonempty open subset. -/
theorem exists_ne_zero_of_analyticOnNhd {f : ℂ → ℂ} {O O' : Set ℂ} (hf : AnalyticOnNhd ℂ f O)
    (hOc : IsPreconnected O) (hO' : IsOpen O') (hO'O : O' ⊆ O) (hne : O'.Nonempty)
    (h : ∃ y ∈ O, f y ≠ 0) : ∃ y ∈ O', f y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y', hy'⟩ := hne
  have hev : f =ᶠ[𝓝 y'] 0 := by
    filter_upwards [hO'.mem_nhds hy'] with z hz using hcon z hz
  obtain ⟨y, hyO, hy⟩ := h
  exact hy (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hOc (hO'O hy') hev hyO)

/-- A disc around `z` inside `D` carrying a branch `g` of `φ_c` with `R(·, g) ≡ 0` and
`S(·, g) ≢ 0`. -/
def RelBranchAt (c : ℂ) (D : Set ℂ) (R S : ℂ → ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ r > 0, ball z r ⊆ D ∧ ∃ g, IsBasinBranch c (ball z r) g ∧
    (∀ y ∈ ball z r, R y (g y) = 0) ∧ ∃ y ∈ ball z r, S y (g y) ≠ 0

/-- **Propagation of a relation along the branches of `φ_c`** through a connected open region. -/
theorem relBranchAt_of_preconnected {c : ℂ} {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hDK : D ⊆ (filledJulia c)ᶜ) {R S : ℂ → ℂ → ℂ}
    (hR : ∀ (O : Set ℂ) (g : ℂ → ℂ), IsOpen O → O ⊆ D → DifferentiableOn ℂ g O →
      AnalyticOnNhd ℂ (fun y => R y (g y)) O)
    (hS : ∀ (O : Set ℂ) (g : ℂ → ℂ), IsOpen O → O ⊆ D → DifferentiableOn ℂ g O →
      AnalyticOnNhd ℂ (fun y => S y (g y)) O)
    {z₀ : ℂ} (h₀ : RelBranchAt c D R S z₀) : ∀ z ∈ D, RelBranchAt c D R S z := by
  set u := {z | RelBranchAt c D R S z} with hudef
  have huo : IsOpen u := by
    rw [Metric.isOpen_iff]
    rintro z ⟨r, hr, hrD, g, hg, hRg, hSg⟩
    refine ⟨r, hr, fun z' hz' => ?_⟩
    have hr' : 0 < r - dist z' z := sub_pos.mpr (mem_ball.mp hz')
    have hsub : ball z' (r - dist z' z) ⊆ ball z r := ball_subset_ball' (by linarith)
    refine ⟨r - dist z' z, hr', hsub.trans hrD, g, hg.mono hsub, fun y hy => hRg y (hsub hy), ?_⟩
    exact exists_ne_zero_of_analyticOnNhd (hS _ g isOpen_ball hrD hg.1)
      (convex_ball z r).isPreconnected isOpen_ball hsub ⟨z', mem_ball_self hr'⟩ hSg
  have hclosed : ∀ z ∈ D, z ∈ closure u → z ∈ u := by
    intro z hzD hzcl
    obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp hDo z hzD
    obtain ⟨z', ⟨r', hr', hr'D, g', hg', hRg', hSg'⟩, hz'z⟩ :=
      Metric.mem_closure_iff.mp hzcl ρ hρ
    have hz'B : z' ∈ ball z ρ := by rw [mem_ball, dist_comm]; exact hz'z
    obtain ⟨G, hG, hGz'⟩ := exists_isBasinBranch_ball (hρD.trans hDK) z' (g' z')
    have hOo : IsOpen (ball z' r' ∩ ball z ρ) := isOpen_ball.inter isOpen_ball
    have hOc : IsPreconnected (ball z' r' ∩ ball z ρ) :=
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    have hz'O : z' ∈ ball z' r' ∩ ball z ρ := ⟨mem_ball_self hr', hz'B⟩
    have hgG : EqOn g' G (ball z' r' ∩ ball z ρ) :=
      IsBasinBranch.eqOn_of_preconnected hOo hOc (inter_subset_right.trans (hρD.trans hDK))
        (hg'.mono inter_subset_left) (hG.mono inter_subset_right) hz'O hGz'.symm
    refine ⟨ρ, hρ, hρD, G, hG, ?_, ?_⟩
    · have hev : (fun y => R y (G y)) =ᶠ[𝓝 z'] 0 := by
        filter_upwards [hOo.mem_nhds hz'O] with y hy
        rw [← hgG hy]
        exact hRg' y hy.1
      exact fun y hy => (hR _ G isOpen_ball hρD hG.1).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball z ρ).isPreconnected hz'B hev hy
    · obtain ⟨y, hyO, hy⟩ := exists_ne_zero_of_analyticOnNhd (hS _ g' isOpen_ball hr'D hg'.1)
        (convex_ball z' r').isPreconnected hOo inter_subset_left ⟨z', hz'O⟩ hSg'
      exact ⟨y, hyO.2, by rwa [← hgG hyO]⟩
  have huD : u ⊆ D := fun z ⟨r, hr, hrD, _⟩ => hrD (mem_ball_self hr)
  have hDsub : D ⊆ u ∪ (closure u)ᶜ := fun z hz => by
    by_cases h : z ∈ closure u
    · exact Or.inl (hclosed z hz h)
    · exact Or.inr h
  have hdisj : Disjoint u (closure u)ᶜ := (disjoint_compl_right (a := closure u)).mono_left
    subset_closure
  exact hDc.subset_left_of_subset_union huo isClosed_closure.isOpen_compl hdisj hDsub
    ⟨z₀, huD h₀, h₀⟩

/-! ### Zeros and moduli of branches -/

/-- The zero function is a branch. -/
theorem isBasinBranch_zero (c : ℂ) (O : Set ℂ) : IsBasinBranch c O fun _ => 0 :=
  ⟨differentiableOn_const 0, fun z _ => by simp⟩

/-- **A branch vanishing at one point of a connected open set vanishes nowhere else, or
everywhere.** -/
theorem IsBasinBranch.ne_zero_of_ne_zero {c : ℂ} {O : Set ℂ} {g : ℂ → ℂ} (hOo : IsOpen O)
    (hOc : IsPreconnected O) (hOK : O ⊆ (filledJulia c)ᶜ) (hg : IsBasinBranch c O g) {z₀ : ℂ}
    (hz₀ : z₀ ∈ O) (h₀ : g z₀ ≠ 0) : ∀ z ∈ O, g z ≠ 0 := by
  set T := {z | g z ≠ 0 ∧ z ∈ O} with hTdef
  have hTo : IsOpen T := by
    have hcont : ContinuousOn g O := hg.1.continuousOn
    rw [Metric.isOpen_iff]
    rintro z ⟨hz, hzO⟩
    obtain ⟨r₁, hr₁, hr₁O⟩ := Metric.isOpen_iff.mp hOo z hzO
    obtain ⟨r₂, hr₂, hr₂g⟩ := Metric.eventually_nhds_iff.mp
      ((hcont.continuousAt (hOo.mem_nhds hzO)).eventually_ne hz)
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂, fun y hy =>
      ⟨hr₂g (lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)),
        hr₁O (ball_subset_ball (min_le_left _ _) hy)⟩⟩
  have hclosed : ∀ z ∈ O, z ∈ closure T → z ∈ T := by
    intro z hzO hzcl
    refine ⟨fun hz0 => ?_, hzO⟩
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOo z hzO
    have hzero : EqOn g (fun _ => 0) (ball z r) :=
      IsBasinBranch.eqOn_of_preconnected isOpen_ball (convex_ball z r).isPreconnected
        (hrO.trans hOK) (hg.mono hrO) (isBasinBranch_zero c _) (mem_ball_self hr) hz0
    obtain ⟨y, ⟨hy, -⟩, hyz⟩ := Metric.mem_closure_iff.mp hzcl r hr
    exact hy (hzero (by rw [mem_ball, dist_comm]; exact hyz))
  have hsub : O ⊆ T ∪ (closure T)ᶜ := fun z hz => by
    by_cases h : z ∈ closure T
    · exact Or.inl (hclosed z hz h)
    · exact Or.inr h
  have hdisj : Disjoint T (closure T)ᶜ :=
    (disjoint_compl_right (a := closure T)).mono_left subset_closure
  intro z hz
  exact (hOc.subset_left_of_subset_union hTo isClosed_closure.isOpen_compl hdisj hsub
    ⟨z₀, hz₀, h₀, hz₀⟩ hz).1

/-- Two real-linear functionals on `ℂ` with the same complex gradient agree. -/
theorem realLinear_eq_of_grad_eq {A A' : ℂ →L[ℝ] ℝ}
    (h : (A 1 : ℂ) - Complex.I * (A Complex.I : ℂ) = (A' 1 : ℂ) - Complex.I * (A' Complex.I : ℂ)) :
    A = A' := by
  have h1 : A 1 = A' 1 := by
    have := congrArg Complex.re h
    simpa using this
  have hI : A Complex.I = A' Complex.I := by
    have := congrArg Complex.im h
    simpa using this
  ext u
  have hu : u = (u.re : ℝ) • (1 : ℂ) + (u.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  rw [hu, map_add, map_smul, map_smul, map_add, map_smul, map_smul, h1, hI]

/-- **Modulus of a branch.**  A nowhere vanishing branch of `φ_c` on a connected open subset of the
basin has modulus `C·e^{G_c}` for a constant `C > 0`: `log‖g‖` and `G_c` have the same gradient
`g'/g = ω = 2∂G_c`. -/
theorem IsBasinBranch.exists_norm_eq_mul_exp {c : ℂ} {O : Set ℂ} {g : ℂ → ℂ} (hOo : IsOpen O)
    (hOc : IsPreconnected O) (hOK : O ⊆ (filledJulia c)ᶜ) (hg : IsBasinBranch c O g)
    (hne : ∀ z ∈ O, g z ≠ 0) :
    ∃ C > 0, ∀ z ∈ O, ‖g z‖ = C * Real.exp (greenFunctionDyn c z) := by
  have hgd : ∀ z ∈ O, DifferentiableAt ℂ g z := fun z hz => hg.1.differentiableAt (hOo.mem_nhds hz)
  have hlogd : ∀ z ∈ O, DifferentiableAt ℝ (fun w => Real.log ‖g w‖) z := fun z hz =>
    (differentiableAt_log_norm (hne z hz)).comp z ((hgd z hz).restrictScalars ℝ)
  have hGd : ∀ z ∈ O, DifferentiableAt ℝ (greenFunctionDyn c) z := fun z hz =>
    differentiableAt_greenFunctionDyn_basin (hOK hz)
  obtain ⟨a, ha⟩ := hOo.exists_eq_add_of_fderiv_eq hOc
    (fun z hz => (hlogd z hz).differentiableWithinAt)
    (fun z hz => (hGd z hz).differentiableWithinAt) (fun z hz => by
      apply realLinear_eq_of_grad_eq
      change realGrad (fun w => Real.log ‖g w‖) z = realGrad (greenFunctionDyn c) z
      have hcomp : realGrad ((fun w : ℂ => Real.log ‖w‖) ∘ g) z =
          realGrad (fun w : ℂ => Real.log ‖w‖) (g z) * deriv g z :=
        realGrad_comp (differentiableAt_log_norm (hne z hz)) (hgd z hz)
      change realGrad ((fun w : ℂ => Real.log ‖w‖) ∘ g) z = _
      rw [hcomp, realGrad_log_norm (hne z hz), hg.2 z hz,
        ← greenLogDeriv_eq_realGrad_greenFunctionDyn (hOK hz)]
      field_simp [hne z hz])
  refine ⟨Real.exp a, Real.exp_pos a, fun z hz => ?_⟩
  have hpos : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z hz)
  have hz' : Real.log ‖g z‖ = greenFunctionDyn c z + a := ha hz
  rw [← Real.exp_log hpos, hz', Real.exp_add, mul_comm]

/-! ### Propagation for pairs of branches -/

/-- A disc around `z` inside `D` carrying branches `g₁` of `φ_{c₁}` and `g₂` of `φ_{c₂}` with
`R(·, g₁, g₂) ≡ 0` and `S(·, g₁, g₂) ≢ 0`. -/
def RelBranchPairAt (c₁ c₂ : ℂ) (D : Set ℂ) (R S : ℂ → ℂ → ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ r > 0, ball z r ⊆ D ∧ ∃ g₁ g₂, IsBasinBranch c₁ (ball z r) g₁ ∧
    IsBasinBranch c₂ (ball z r) g₂ ∧ (∀ y ∈ ball z r, R y (g₁ y) (g₂ y) = 0) ∧
    ∃ y ∈ ball z r, S y (g₁ y) (g₂ y) ≠ 0

/-- **Propagation of a relation along pairs of branches** through a connected open region lying
in both basins. -/
theorem relBranchPairAt_of_preconnected {c₁ c₂ : ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hDK₁ : D ⊆ (filledJulia c₁)ᶜ) (hDK₂ : D ⊆ (filledJulia c₂)ᶜ)
    {R S : ℂ → ℂ → ℂ → ℂ}
    (hR : ∀ (O : Set ℂ) (g₁ g₂ : ℂ → ℂ), IsOpen O → O ⊆ D → DifferentiableOn ℂ g₁ O →
      DifferentiableOn ℂ g₂ O → AnalyticOnNhd ℂ (fun y => R y (g₁ y) (g₂ y)) O)
    (hS : ∀ (O : Set ℂ) (g₁ g₂ : ℂ → ℂ), IsOpen O → O ⊆ D → DifferentiableOn ℂ g₁ O →
      DifferentiableOn ℂ g₂ O → AnalyticOnNhd ℂ (fun y => S y (g₁ y) (g₂ y)) O)
    {z₀ : ℂ} (h₀ : RelBranchPairAt c₁ c₂ D R S z₀) : ∀ z ∈ D, RelBranchPairAt c₁ c₂ D R S z := by
  set u := {z | RelBranchPairAt c₁ c₂ D R S z} with hudef
  have huo : IsOpen u := by
    rw [Metric.isOpen_iff]
    rintro z ⟨r, hr, hrD, g₁, g₂, hg₁, hg₂, hRg, hSg⟩
    refine ⟨r, hr, fun z' hz' => ?_⟩
    have hr' : 0 < r - dist z' z := sub_pos.mpr (mem_ball.mp hz')
    have hsub : ball z' (r - dist z' z) ⊆ ball z r := ball_subset_ball' (by linarith)
    refine ⟨r - dist z' z, hr', hsub.trans hrD, g₁, g₂, hg₁.mono hsub, hg₂.mono hsub,
      fun y hy => hRg y (hsub hy), ?_⟩
    exact exists_ne_zero_of_analyticOnNhd (hS _ g₁ g₂ isOpen_ball hrD hg₁.1 hg₂.1)
      (convex_ball z r).isPreconnected isOpen_ball hsub ⟨z', mem_ball_self hr'⟩ hSg
  have hclosed : ∀ z ∈ D, z ∈ closure u → z ∈ u := by
    intro z hzD hzcl
    obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp hDo z hzD
    obtain ⟨z', ⟨r', hr', hr'D, g₁, g₂, hg₁, hg₂, hRg, hSg⟩, hz'z⟩ :=
      Metric.mem_closure_iff.mp hzcl ρ hρ
    have hz'B : z' ∈ ball z ρ := by rw [mem_ball, dist_comm]; exact hz'z
    obtain ⟨G₁, hG₁, hG₁z'⟩ := exists_isBasinBranch_ball (hρD.trans hDK₁) z' (g₁ z')
    obtain ⟨G₂, hG₂, hG₂z'⟩ := exists_isBasinBranch_ball (hρD.trans hDK₂) z' (g₂ z')
    have hOo : IsOpen (ball z' r' ∩ ball z ρ) := isOpen_ball.inter isOpen_ball
    have hOc : IsPreconnected (ball z' r' ∩ ball z ρ) :=
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    have hz'O : z' ∈ ball z' r' ∩ ball z ρ := ⟨mem_ball_self hr', hz'B⟩
    have h₁ : EqOn g₁ G₁ (ball z' r' ∩ ball z ρ) :=
      IsBasinBranch.eqOn_of_preconnected hOo hOc (inter_subset_right.trans (hρD.trans hDK₁))
        (hg₁.mono inter_subset_left) (hG₁.mono inter_subset_right) hz'O hG₁z'.symm
    have h₂ : EqOn g₂ G₂ (ball z' r' ∩ ball z ρ) :=
      IsBasinBranch.eqOn_of_preconnected hOo hOc (inter_subset_right.trans (hρD.trans hDK₂))
        (hg₂.mono inter_subset_left) (hG₂.mono inter_subset_right) hz'O hG₂z'.symm
    refine ⟨ρ, hρ, hρD, G₁, G₂, hG₁, hG₂, ?_, ?_⟩
    · have hev : (fun y => R y (G₁ y) (G₂ y)) =ᶠ[𝓝 z'] 0 := by
        filter_upwards [hOo.mem_nhds hz'O] with y hy
        rw [← h₁ hy, ← h₂ hy]
        exact hRg y hy.1
      exact fun y hy =>
        (hR _ G₁ G₂ isOpen_ball hρD hG₁.1 hG₂.1).eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_ball z ρ).isPreconnected hz'B hev hy
    · obtain ⟨y, hyO, hy⟩ := exists_ne_zero_of_analyticOnNhd
        (hS _ g₁ g₂ isOpen_ball hr'D hg₁.1 hg₂.1) (convex_ball z' r').isPreconnected hOo
        inter_subset_left ⟨z', hz'O⟩ hSg
      exact ⟨y, hyO.2, by rwa [← h₁ hyO, ← h₂ hyO]⟩
  have huD : u ⊆ D := fun z ⟨r, hr, hrD, _⟩ => hrD (mem_ball_self hr)
  have hDsub : D ⊆ u ∪ (closure u)ᶜ := fun z hz => by
    by_cases h : z ∈ closure u
    · exact Or.inl (hclosed z hz h)
    · exact Or.inr h
  have hdisj : Disjoint u (closure u)ᶜ := (disjoint_compl_right (a := closure u)).mono_left
    subset_closure
  exact hDc.subset_left_of_subset_union huo isClosed_closure.isOpen_compl hdisj hDsub
    ⟨z₀, huD h₀, h₀⟩

end Bottcher
