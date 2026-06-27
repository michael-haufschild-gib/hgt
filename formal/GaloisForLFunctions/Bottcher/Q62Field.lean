/-
# Field-4 / Field-7 scaffolding: the Böttcher coordinates inside the meromorphic field `M`

Places the genuine Böttcher coordinate `φ_c` as an element of the carrier field `M = meroField U`,
for a common exterior region `U` on which both `φ_{c₁}` and `φ_{c₂}` are analytic. This is the bridge
from the analytic layer (`bottcherCoord`, analytic on `escapeOpen`) to the algebraic carrier
(`meroField`) the q62 statement is instantiated over: `φ_c` is the germ of the actual function, not a
formal symbol.
-/
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.Topology.Separation.Connected

open Filter Topology Set

namespace Bottcher

variable {U : Set ℂ}

/-- The Böttcher coordinate `φ_c` as an element of `analyticSubring U`, valid when `U ⊆ escapeOpen c`
(where `φ_c` is analytic and nowhere zero). The genuine function as a germ. -/
noncomputable def phiAnalytic (c : ℂ) (hU : U ⊆ escapeOpen c) : analyticSubring U :=
  ⟨Germ.coeRingHom (𝓟 U) (bottcherCoord c),
   ⟨bottcherCoord c, (analyticOnNhd_bottcherCoord_full c).mono hU, rfl⟩⟩

/-- The genuine Böttcher coordinate `φ_c` as an element of the meromorphic field `M = meroField U` —
the actual analytic function, embedded via the fraction-field map. This is the `φ c` the q62
instantiation feeds to `q62_independence`. -/
noncomputable def phiMero (c : ℂ) (hU : U ⊆ escapeOpen c) : meroField U :=
  algebraMap (analyticSubring U) (meroField U) (phiAnalytic c hU)

/-! ### A connected base `U` near `∞`

We need a connected open `U ⊆ escapeOpen c₁ ∩ escapeOpen c₂` to place both `φ_{c₁}, φ_{c₂}` in the
same field `M = meroField U`. We take `U` to be a *ball* deep in the common exterior: convexity makes
it connected (the full annular exterior `{‖z‖ > R}` connectedness is not in Mathlib, and a ball
suffices — the connected basin `Ω_c` propagates any germ relation to the global function by the
identity theorem). -/

/-- Real center of norm `3 + max ‖c₁‖ ‖c₂‖`, deep in the common exterior. -/
noncomputable def deepCenter (c₁ c₂ : ℂ) : ℂ := ((3 + max ‖c₁‖ ‖c₂‖ : ℝ) : ℂ)

/-- A unit ball around `deepCenter`, lying inside `escapeOpen c₁ ∩ escapeOpen c₂`. Convex ⟹
connected; the base `U` for placing both `φ_{c₁}, φ_{c₂}` in the same field `M = meroField U`. -/
noncomputable def deepBall (c₁ c₂ : ℂ) : Set ℂ := Metric.ball (deepCenter c₁ c₂) 1

theorem norm_deepCenter (c₁ c₂ : ℂ) : ‖deepCenter c₁ c₂‖ = 3 + max ‖c₁‖ ‖c₂‖ := by
  rw [deepCenter, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Every point of `deepBall` has norm `> 2 + max ‖c₁‖ ‖c₂‖`. -/
theorem deepBall_lt_norm {c₁ c₂ z : ℂ} (hz : z ∈ deepBall c₁ c₂) :
    2 + max ‖c₁‖ ‖c₂‖ < ‖z‖ := by
  rw [deepBall, Metric.mem_ball, Complex.dist_eq] at hz
  have h1 : ‖deepCenter c₁ c₂‖ - ‖z‖ ≤ ‖deepCenter c₁ c₂ - z‖ := norm_sub_norm_le _ _
  rw [norm_deepCenter, norm_sub_rev] at h1
  linarith

theorem deepBall_subset_escapeOpen_left (c₁ c₂ : ℂ) : deepBall c₁ c₂ ⊆ escapeOpen c₁ := by
  intro z hz
  simp only [escapeOpen, mem_setOf_eq]
  have h := deepBall_lt_norm hz
  have hm : max 2 ‖c₁‖ ≤ 2 + max ‖c₁‖ ‖c₂‖ := by
    have := le_max_left ‖c₁‖ ‖c₂‖; have := norm_nonneg c₁; have := norm_nonneg c₂
    apply max_le <;> linarith
  linarith

theorem deepBall_subset_escapeOpen_right (c₁ c₂ : ℂ) : deepBall c₁ c₂ ⊆ escapeOpen c₂ := by
  intro z hz
  simp only [escapeOpen, mem_setOf_eq]
  have h := deepBall_lt_norm hz
  have hm : max 2 ‖c₂‖ ≤ 2 + max ‖c₁‖ ‖c₂‖ := by
    have := le_max_right ‖c₁‖ ‖c₂‖; have := norm_nonneg c₁; have := norm_nonneg c₂
    apply max_le <;> linarith
  linarith

theorem isOpen_deepBall (c₁ c₂ : ℂ) : IsOpen (deepBall c₁ c₂) := Metric.isOpen_ball

theorem isPreconnected_deepBall (c₁ c₂ : ℂ) : IsPreconnected (deepBall c₁ c₂) :=
  (convex_ball _ _).isPreconnected

theorem deepBall_nonempty (c₁ c₂ : ℂ) : (deepBall c₁ c₂).Nonempty :=
  Metric.nonempty_ball.mpr one_pos

theorem deepBall_infinite (c₁ c₂ : ℂ) : (deepBall c₁ c₂).Infinite := by
  have hpc : IsPreconnected (deepBall c₁ c₂) := isPreconnected_deepBall c₁ c₂
  have hc : deepCenter c₁ c₂ ∈ deepBall c₁ c₂ := Metric.mem_ball_self one_pos
  have hc2 : deepCenter c₁ c₂ + 1 / 2 ∈ deepBall c₁ c₂ := by
    rw [deepBall, Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left]
    norm_num [Complex.norm_div, Complex.norm_ofNat]
  exact IsPreconnected.infinite_of_nontrivial hpc
    ⟨deepCenter c₁ c₂, hc, deepCenter c₁ c₂ + 1 / 2, hc2,
     by intro h; have h2 : (1 / 2 : ℂ) = 0 := (by linear_combination -h); norm_num at h2⟩

/-! ### Basic facts about the coordinates as elements of `M` -/

/-- The Böttcher coordinate is a **nonzero** element of `M`: its germ is the germ of the
nowhere-vanishing `φ_c` on the nonempty `U`, and the fraction-field map is injective. This is the
`F ≠ 0` / `G ≠ 0` datum the obstruction (`q62_disconnected_both`, `algIndep_of_unbounded_monodromy`)
requires. -/
theorem phiMero_ne_zero {U : Set ℂ} (_hUo : IsOpen U) (_hUc : IsPreconnected U)
    (hUne : U.Nonempty)
    {c : ℂ} (hU : U ⊆ escapeOpen c) : phiMero c hU ≠ 0 := by
  haveI := isDomain_analyticSubring U _hUo _hUc hUne
  intro h
  have hinj := IsFractionRing.injective (analyticSubring U) (meroField U)
  have h0 : phiAnalytic c hU = 0 := by apply hinj; rw [map_zero]; exact h
  have hg : (Germ.coeRingHom (𝓟 U) (bottcherCoord c)) = (0 : Germ (𝓟 U) ℂ) := by
    have := congrArg (Subtype.val) h0
    rwa [ZeroMemClass.coe_zero] at this
  rw [show Germ.coeRingHom (𝓟 U) (bottcherCoord c) = (↑(bottcherCoord c) : Germ (𝓟 U) ℂ) from rfl,
      ← Germ.coe_zero, Germ.coe_eq] at hg
  obtain ⟨z, hz⟩ := hUne
  exact bottcherCoord_ne_zero c z (eventually_principal.mp hg z hz)

/-- Specialised to the connected base `deepBall`: each Böttcher coordinate is nonzero in `M`. -/
theorem phiMero_deepBall_ne_zero (c₁ c₂ : ℂ) {c : ℂ}
    (hU : deepBall c₁ c₂ ⊆ escapeOpen c) : phiMero c hU ≠ 0 :=
  phiMero_ne_zero (isOpen_deepBall c₁ c₂) (isPreconnected_deepBall c₁ c₂)
    (deepBall_nonempty c₁ c₂) hU

/-! ### Field-5 evaluation bridge: polynomial-in-`φ_c` evaluation = germ of the function

These connect *algebraic* evaluation in `M` to the *analytic* function `z ↦ p(φ_c(z))`, so a
relation in `M` is literally a vanishing function — the analytic content of `NoRelation`. -/

/-- `z ↦ p(φ_c(z))` is analytic on `U ⊆ escapeOpen c` (a polynomial of the analytic `φ_c`). -/
theorem analyticOnNhd_evalComp (c : ℂ) (hU : U ⊆ escapeOpen c) (p : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z => p.eval (bottcherCoord c z)) U := by
  have h : AnalyticOnNhd ℂ (fun z => Polynomial.aeval (bottcherCoord c z) p) U :=
    ((analyticOnNhd_bottcherCoord_full c).mono hU).aeval_polynomial p
  have heq : (fun z => Polynomial.aeval (bottcherCoord c z) p)
      = (fun z => p.eval (bottcherCoord c z)) := by
    funext z; simp [Polynomial.aeval_def]
  rwa [heq] at h

/-- `ℂ[X] →+* analyticSubring U`, `p ↦` germ of `z ↦ p(φ_c(z))`. -/
noncomputable def evalCompHom (c : ℂ) (hU : U ⊆ escapeOpen c) : Polynomial ℂ →+* analyticSubring U :=
  ((Germ.coeRingHom (𝓟 U)).comp
      (Pi.ringHom (fun z => Polynomial.evalRingHom (bottcherCoord c z)))).codRestrict
    (analyticSubring U) (fun p => ⟨fun z => p.eval (bottcherCoord c z),
      analyticOnNhd_evalComp c hU p, rfl⟩)

theorem evalCompHom_X (c : ℂ) (hU : U ⊆ escapeOpen c) :
    evalCompHom c hU Polynomial.X = phiAnalytic c hU := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 U) (fun z => Polynomial.eval (bottcherCoord c z) Polynomial.X)
     = Germ.coeRingHom (𝓟 U) (bottcherCoord c)
  congr 1; funext z; simp

theorem evalCompHom_C (c : ℂ) (hU : U ⊆ escapeOpen c) (a : ℂ) :
    evalCompHom c hU (Polynomial.C a) = constToAnalytic U a := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 U) (fun z => Polynomial.eval (bottcherCoord c z) (Polynomial.C a))
     = Germ.coeRingHom (𝓟 U) (fun _ => a)
  congr 1; funext z; simp

/-- **Single-coordinate evaluation = germ.** Evaluating a `ℂ`-polynomial `p` at `phiMero c` in `M`
equals the image of the germ of the genuine function `z ↦ p(φ_c(z))` (two ring homs `ℂ[X] → M`
agreeing on `X` and constants). With faithfulness, `p(phiMero c)=0 ⟺ z↦p(φ_c(z))` vanishes on `U`. -/
theorem eval_phiMero (c : ℂ) (hU : U ⊆ escapeOpen c) (p : Polynomial ℂ) :
    (Polynomial.eval₂RingHom
        ((algebraMap (analyticSubring U) (meroField U)).comp (constToAnalytic U)) (phiMero c hU)) p
      = algebraMap (analyticSubring U) (meroField U) (evalCompHom c hU p) := by
  have hext : (Polynomial.eval₂RingHom
        ((algebraMap (analyticSubring U) (meroField U)).comp (constToAnalytic U)) (phiMero c hU))
      = (algebraMap (analyticSubring U) (meroField U)).comp (evalCompHom c hU) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.coe_comp,
        Function.comp_apply, evalCompHom_C]
    · simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.coe_comp,
        Function.comp_apply, evalCompHom_X, phiMero]
  exact RingHom.congr_fun hext p

/-- **Single-coordinate faithfulness (complete).** `phiMero c` is a root of a `ℂ`-polynomial `p` in
`M` iff the genuine function `z ↦ p(φ_c(z))` vanishes on `U`. So an algebraic relation in `M` is
exactly a vanishing analytic function — the bridge that makes `NoRelation`/transcendence over `M` a
statement about the *actual* Böttcher coordinate, not a formal artefact. (Connected-case
faithfulness, single-coordinate; the bivariate-over-`ℂ(z)` version follows the same pattern with
`evalCompHom` in two variables and clearing denominators.) -/
theorem eval_phiMero_eq_zero_iff (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (c : ℂ) (hU : U ⊆ escapeOpen c) (p : Polynomial ℂ) :
    (Polynomial.eval₂RingHom
        ((algebraMap (analyticSubring U) (meroField U)).comp (constToAnalytic U)) (phiMero c hU)) p
      = 0 ↔ EqOn (fun z => p.eval (bottcherCoord c z)) 0 U := by
  rw [eval_phiMero]
  exact meroField_germ_eq_zero_iff U hUo hUc hUne (analyticOnNhd_evalComp c hU p)

/-! ### Bivariate faithfulness: a relation `P(z,φ_{c₁},φ_{c₂})=0` in `M` = a vanishing function -/

/-- **Bivariate analyticity**: `z ↦ P(z, φ_{c₁}(z), φ_{c₂}(z))` is analytic on `U` for any 3-variable
polynomial `P` (`aeval_mvPolynomial` of the analytic coordinate functions). -/
theorem analyticOnNhd_mvEval (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (p : MvPolynomial (Fin 3) ℂ) :
    AnalyticOnNhd ℂ
      (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) p) U := by
  apply AnalyticOnNhd.aeval_mvPolynomial
  intro i; fin_cases i
  · exact fun z _ => analyticAt_id
  · exact fun z hz => (analyticOnNhd_bottcherCoord_full c₁ z (hU₁ hz))
  · exact fun z hz => (analyticOnNhd_bottcherCoord_full c₂ z (hU₂ hz))

/-- The bivariate evaluation ring hom `ℂ[X₀,X₁,X₂] →+* analyticSubring U`,
`P ↦` germ of `z ↦ P(z, φ_{c₁}(z), φ_{c₂}(z))` (coordinates `X₀=z, X₁=φ_{c₁}, X₂=φ_{c₂}`). -/
noncomputable def mvEvalHom (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) :
    MvPolynomial (Fin 3) ℂ →+* analyticSubring U :=
  ((Germ.coeRingHom (𝓟 U)).comp
      (Pi.ringHom (fun z => (MvPolynomial.aeval
        (![z, bottcherCoord c₁ z, bottcherCoord c₂ z])).toRingHom))).codRestrict
    (analyticSubring U) (fun p => ⟨fun z => MvPolynomial.aeval
      (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) p, analyticOnNhd_mvEval c₁ c₂ hU₁ hU₂ p, rfl⟩)

theorem mvEvalHom_X1 (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) :
    mvEvalHom c₁ c₂ hU₁ hU₂ (MvPolynomial.X 1) = phiAnalytic c₁ hU₁ := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 U)
      (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) (MvPolynomial.X 1))
    = Germ.coeRingHom (𝓟 U) (bottcherCoord c₁)
  congr 1; funext z; simp

theorem mvEvalHom_X2 (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) :
    mvEvalHom c₁ c₂ hU₁ hU₂ (MvPolynomial.X 2) = phiAnalytic c₂ hU₂ := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 U)
      (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) (MvPolynomial.X 2))
    = Germ.coeRingHom (𝓟 U) (bottcherCoord c₂)
  congr 1; funext z; simp

/-- **Bivariate faithfulness (complete).** A 3-variable algebraic relation `P(z,φ_{c₁},φ_{c₂})=0`
holds in `M` iff the genuine function `z ↦ P(z,φ_{c₁}(z),φ_{c₂}(z))` vanishes on `U`. This is the full
connected-case faithfulness over `ℂ`: `NoRelation` among `(z,φ_{c₁},φ_{c₂})` in `M` = the actual
algebraic independence of the Böttcher coordinates as functions. (The `ℂ(z)`-coefficient
`NoRelation` form reduces here by clearing denominators and `ℂ[z][W][Y] ≅ MvPolynomial (Fin 3) ℂ`.) -/
theorem mvEval_eq_zero_iff (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) (P : MvPolynomial (Fin 3) ℂ) :
    algebraMap (analyticSubring U) (meroField U) (mvEvalHom c₁ c₂ hU₁ hU₂ P) = 0
      ↔ Set.EqOn (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) P) 0 U :=
  meroField_germ_eq_zero_iff U hUo hUc hUne (analyticOnNhd_mvEval c₁ c₂ hU₁ hU₂ P)

/-- `mvEvalHom` sends `X₀ ↦` the germ of the coordinate `z` (= `polyToAnalytic X`, the base-field
generator). So `(X₀,X₁,X₂) ↦ (z, φ_{c₁}, φ_{c₂})` — every coordinate of the bivariate bridge is
pinned to the genuine objects, completing the identification. -/
theorem mvEvalHom_X0 (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) :
    mvEvalHom c₁ c₂ hU₁ hU₂ (MvPolynomial.X 0) = polyToAnalytic U Polynomial.X := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 U)
      (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) (MvPolynomial.X 0))
    = Germ.coeRingHom (𝓟 U) (fun z => Polynomial.eval z Polynomial.X)
  congr 1; funext z; simp

/-- **Connected-case faithfulness on the concrete base `deepBall`.** A 3-variable relation
`P(z,φ_{c₁},φ_{c₂})=0` holds in `M = meroField (deepBall c₁ c₂)` iff the genuine function vanishes on
`deepBall c₁ c₂`. Directly usable for the connected-case assembly: `NoRelation` over the concrete `M`
reduces (via this faithfulness) to the algebraic independence of the Böttcher *functions* on
`deepBall` — precisely the natural-boundary/E–vS step. -/
theorem mvEval_deepBall_eq_zero_iff (c₁ c₂ : ℂ) (P : MvPolynomial (Fin 3) ℂ) :
    algebraMap (analyticSubring (deepBall c₁ c₂)) (meroField (deepBall c₁ c₂))
        (mvEvalHom c₁ c₂ (deepBall_subset_escapeOpen_left c₁ c₂)
          (deepBall_subset_escapeOpen_right c₁ c₂) P) = 0
      ↔ Set.EqOn (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) P) 0
          (deepBall c₁ c₂) :=
  mvEval_eq_zero_iff (isOpen_deepBall c₁ c₂) (isPreconnected_deepBall c₁ c₂)
    (deepBall_nonempty c₁ c₂) c₁ c₂ _ _ P

/-- **Connected-case reduction (MvPolynomial form).** The algebraic independence of the Böttcher
coordinates in `M = meroField (deepBall c₁ c₂)` follows *exactly* from the algebraic independence of
the Böttcher **functions** on `deepBall` — the latter being the cited connected-case
natural-boundary/E–vS theorem (arXiv:0810.2260). All the algebra/field machinery is discharged here
by `mvEval_deepBall_eq_zero_iff` (faithfulness); the single remaining input `hFunIndep` is precisely
the analytic theorem. This isolates the connected case to exactly the E–vS continuation step. -/
theorem q62_connected_of_functional_independence (c₁ c₂ : ℂ)
    (hFunIndep : ∀ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 →
      ¬ Set.EqOn (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) P)
        0 (deepBall c₁ c₂)) :
    ∀ P : MvPolynomial (Fin 3) ℂ,
      algebraMap (analyticSubring (deepBall c₁ c₂)) (meroField (deepBall c₁ c₂))
        (mvEvalHom c₁ c₂ (deepBall_subset_escapeOpen_left c₁ c₂)
          (deepBall_subset_escapeOpen_right c₁ c₂) P) = 0 → P = 0 := by
  intro P hP
  by_contra hne
  exact hFunIndep P hne ((mvEval_deepBall_eq_zero_iff c₁ c₂ P).mp hP)

/-- The `X₁` coordinate of the bivariate bridge maps to `phiMero c₁` (= `F` of `NoRelation`) in `M`. -/
theorem algebraMap_mvEvalHom_X1 (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) :
    algebraMap (analyticSubring U) (meroField U) (mvEvalHom c₁ c₂ hU₁ hU₂ (MvPolynomial.X 1))
      = phiMero c₁ hU₁ := by
  rw [mvEvalHom_X1]; rfl

/-- The `X₂` coordinate maps to `phiMero c₂` (= `G` of `NoRelation`) in `M`. -/
theorem algebraMap_mvEvalHom_X2 (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) :
    algebraMap (analyticSubring U) (meroField U) (mvEvalHom c₁ c₂ hU₁ hU₂ (MvPolynomial.X 2))
      = phiMero c₂ hU₂ := by
  rw [mvEvalHom_X2]; rfl

/-- `mvEvalHom` sends a constant `C a ↦ constToAnalytic a` (the constant germ): the scalars `ℂ`
embed compatibly, completing the characterization `(C a, X₀, X₁, X₂) ↦ (a, z, φ_{c₁}, φ_{c₂})`. -/
theorem mvEvalHom_C (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) (a : ℂ) :
    mvEvalHom c₁ c₂ hU₁ hU₂ (MvPolynomial.C a) = constToAnalytic U a := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 U)
      (fun z => MvPolynomial.aeval (![z, bottcherCoord c₁ z, bottcherCoord c₂ z]) (MvPolynomial.C a))
    = Germ.coeRingHom (𝓟 U) (fun _ => a)
  congr 1; funext z; simp

end Bottcher
