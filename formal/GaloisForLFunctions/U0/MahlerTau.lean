/-
# The Mahler operator `τ` on `meroField(escapeOpen c)`

Instantiates the abstract carrier of `carrier_norm_relation`: the field `L = meroField(escapeOpen c)`
with the Mahler operator `τ` = precomposition by `z ↦ z²+c`. Built by extending the parallel agent's
`precompAnalytic` (the precomposition ring endomorphism of `analyticSubring`, valid for any analytic
self-map) to the fraction field via `IsLocalization.map`, using the injectivity established here
(`eqZero_of_comp_quadratic_eqZero` at the germ level).
-/
import GaloisForLFunctions.U0.MahlerCarrier
import GaloisForLFunctions.U0.MahlerMinpoly
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.Bottcher.Q62Field

open Polynomial Bottcher Set Filter

namespace MahlerPolynomial

variable (c : ℂ)

/-- `quadratic c` is analytic on `escapeOpen c`. -/
theorem analyticOnNhd_quadratic_escapeOpen : AnalyticOnNhd ℂ (quadratic c) (escapeOpen c) :=
  fun z _ => analyticAt_quadratic c z

/-- `quadratic c` maps `escapeOpen c` into itself. -/
theorem mapsTo_quadratic_escapeOpen : Set.MapsTo (quadratic c) (escapeOpen c) (escapeOpen c) :=
  fun _ hz => PhiMahler.quadratic_mem_escapeOpen hz

/-- **Precomposition by `quadratic c` is injective on `analyticSubring (escapeOpen c)` (PROVED).**
A ring endomorphism of a domain is injective iff its kernel is trivial; here `precompAnalytic a = 0`
unpacks (via the germ representation `a = ↑f` and `Germ.coe_eq`) to `f(z²+c) = 0` on `escapeOpen`,
which `eqZero_of_comp_quadratic_eqZero` forces to `f ≡ 0`, hence `a = 0`. This is the
nonzerodivisor-preservation needed to lift `precompAnalytic` to the fraction field. -/
theorem precompAnalytic_quadratic_injective :
    Function.Injective (precompAnalytic (analyticOnNhd_quadratic_escapeOpen c)
      (mapsTo_quadratic_escapeOpen c)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, hf, hfa⟩ := a.2
  have hfa' : (↑f : Germ (𝓟 (escapeOpen c)) ℂ) = (a : Germ (𝓟 (escapeOpen c)) ℂ) := hfa
  have hgerm0 : (a : Germ (𝓟 (escapeOpen c)) ℂ).compTendsto (quadratic c)
      (tendsto_principal_principal.mpr (mapsTo_quadratic_escapeOpen c)) = 0 := by
    rw [← precompAnalytic_coe (analyticOnNhd_quadratic_escapeOpen c)
      (mapsTo_quadratic_escapeOpen c) a, ha, ZeroMemClass.coe_zero]
  rw [← hfa', Germ.coe_compTendsto, ← Germ.coe_zero, Germ.coe_eq, eventuallyEq_principal] at hgerm0
  have hf0 : ∀ z ∈ escapeOpen c, f z = 0 :=
    eqZero_of_comp_quadratic_eqZero hf (fun z hz => by
      have := hgerm0 hz; simpa [Function.comp_apply, quadratic_apply, Pi.zero_apply] using this)
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← hfa', ← Germ.coe_zero, Germ.coe_eq, eventuallyEq_principal]
  exact hf0

/-- `escapeOpen c` is nonempty (contains the real point `max 2 ‖c‖ + 1`). -/
theorem escapeOpen_nonempty : (escapeOpen c).Nonempty :=
  ⟨((max 2 ‖c‖ + 1 : ℝ) : ℂ), by
    show max 2 ‖c‖ < ‖((max 2 ‖c‖ + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith⟩

/-- **The Mahler operator `τ` on `meroField(escapeOpen c)` (PROVED).** Precomposition by `z ↦ z²+c`,
extended from `analyticSubring` (the parallel agent's `precompAnalytic`) to the fraction field
`meroField = FractionRing(analyticSubring)` by `IsLocalization.map`, using
`precompAnalytic_quadratic_injective` to verify nonzerodivisor preservation. This is the concrete `τ`
the abstract `carrier_norm_relation` consumes. -/
noncomputable def mahlerTau :
    letI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
      (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
    meroField (escapeOpen c) →+* meroField (escapeOpen c) :=
  letI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
    (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
  IsLocalization.map (meroField (escapeOpen c))
    (precompAnalytic (analyticOnNhd_quadratic_escapeOpen c) (mapsTo_quadratic_escapeOpen c))
    (by
      intro x hx
      rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
      rw [mem_nonZeroDivisors_iff_ne_zero] at hx
      exact fun h => hx (precompAnalytic_quadratic_injective c
        (show _ = _ by rw [h, map_zero])))

/-- **`τ` on a polynomial germ is the germ of the Mahler-substituted polynomial (PROVED).**
`precompAnalytic(polyToAnalytic p) = polyToAnalytic(p(z²+c))`: precomposition by `z↦z²+c` of the
eval-germ of `p` is the eval-germ of `p∘(X²+c)`, since `p.eval(z²+c) = (p.comp(X²+c)).eval z`. This is
the polynomial-level core of `hcompat` (`τ` restricts to `mahlerHom` on `ℂ(z)`). -/
theorem precompAnalytic_polyToAnalytic (p : Polynomial ℂ) :
    precompAnalytic (analyticOnNhd_quadratic_escapeOpen c) (mapsTo_quadratic_escapeOpen c)
      (polyToAnalytic (escapeOpen c) p)
    = polyToAnalytic (escapeOpen c) (p.comp (X ^ 2 + C c)) := by
  apply Subtype.ext
  rw [precompAnalytic_coe]
  show (↑(fun z => p.eval z) : Germ (𝓟 (escapeOpen c)) ℂ).compTendsto (quadratic c)
      (tendsto_principal_principal.mpr (mapsTo_quadratic_escapeOpen c))
      = (↑(fun z => (p.comp (X ^ 2 + C c)).eval z) : Germ (𝓟 (escapeOpen c)) ℂ)
  rw [Germ.coe_compTendsto]
  congr 1
  funext z
  simp only [Function.comp_apply, quadratic_apply, eval_comp, eval_add, eval_pow, eval_X, eval_C]

/-- `escapeOpen c` is infinite (contains an injective real sequence). -/
theorem escapeOpen_infinite : (escapeOpen c).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((max 2 ‖c‖ + 1 + n : ℝ) : ℂ))
  · intro a b hab
    have h1 : (max 2 ‖c‖ + 1 + (a : ℝ)) = (max 2 ‖c‖ + 1 + (b : ℝ)) := Complex.ofReal_injective hab
    exact_mod_cast (by linarith : (a : ℝ) = (b : ℝ))
  · intro n
    show max 2 ‖c‖ < ‖((max 2 ‖c‖ + 1 + (n : ℝ) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := le_max_left 2 ‖c‖; positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- **`τ` on a polynomial eval-germ (PROVED).** `τ(polyToMero p) = polyToMero(p(z²+c))`: unfolding
`polyToMero = algebraMap ∘ polyToAnalytic`, `IsLocalization.map_eq` reduces `τ` to `precompAnalytic`,
which `precompAnalytic_polyToAnalytic` evaluates. -/
theorem mahlerTau_polyToMero (p : Polynomial ℂ) :
    haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
      (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
    mahlerTau c (polyToMero (escapeOpen c) p)
      = polyToMero (escapeOpen c) (p.comp (X ^ 2 + C c)) := by
  haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
    (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
  show mahlerTau c ((algebraMap (analyticSubring (escapeOpen c)) (meroField (escapeOpen c))).comp
      (polyToAnalytic (escapeOpen c)) p) = _
  rw [RingHom.comp_apply]
  unfold mahlerTau
  rw [IsLocalization.map_eq, precompAnalytic_polyToAnalytic]
  rfl

/-- **`τ` restricts to `mahlerHom` on `ℂ(z)` (PROVED — the carrier `hcompat`).** Under the base-field
embedding `ratfuncToMero : ℂ(z) ↪ meroField`, `τ(ratfuncToMero k) = ratfuncToMero(mahlerHom k)`. By
`IsLocalization.ringHom_ext` it suffices to check on `ℂ[z]`, where both sides equal `polyToMero(p(z²+c))`
(`mahlerTau_polyToMero` on the left; `mahlerHom_algebraMap` on the right). This is the `hcompat`
hypothesis of `carrier_norm_relation`. -/
theorem mahlerTau_hcompat (k : RatFunc ℂ) :
    haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
      (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
    mahlerTau c (ratfuncToMero (escapeOpen c) (isOpen_escapeOpen c)
        (isPreconnected_escapeOpen c) (escapeOpen_nonempty c) (escapeOpen_infinite c) k)
      = ratfuncToMero (escapeOpen c) (isOpen_escapeOpen c) (isPreconnected_escapeOpen c)
        (escapeOpen_nonempty c) (escapeOpen_infinite c) (mahlerHom c k) := by
  haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
    (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
  have key : (mahlerTau c).comp (ratfuncToMero (escapeOpen c) (isOpen_escapeOpen c)
        (isPreconnected_escapeOpen c) (escapeOpen_nonempty c) (escapeOpen_infinite c))
      = (ratfuncToMero (escapeOpen c) (isOpen_escapeOpen c) (isPreconnected_escapeOpen c)
        (escapeOpen_nonempty c) (escapeOpen_infinite c)).comp (mahlerHom c).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [ratfuncToMero_algebraMap_polynomial, mahlerHom_algebraMap,
        ratfuncToMero_algebraMap_polynomial]
    exact mahlerTau_polyToMero c p
  exact RingHom.congr_fun key k

/-- **`precompAnalytic(φ_c germ) = (φ_c germ)²` (PROVED).** Precomposition by `z↦z²+c` of the Böttcher
germ equals its square, because `φ_c(z²+c) = φ_c(z)²` on the escape region (`bottcherCoord_quadratic`).
This is the functional equation at the germ level. -/
theorem precompAnalytic_phiAnalytic :
    precompAnalytic (analyticOnNhd_quadratic_escapeOpen c) (mapsTo_quadratic_escapeOpen c)
      (phiAnalytic c (Set.Subset.refl (escapeOpen c)))
    = (phiAnalytic c (Set.Subset.refl (escapeOpen c))) ^ 2 := by
  apply Subtype.ext
  rw [precompAnalytic_coe, SubmonoidClass.coe_pow]
  show (↑(bottcherCoord c) : Germ (𝓟 (escapeOpen c)) ℂ).compTendsto (quadratic c)
      (tendsto_principal_principal.mpr (mapsTo_quadratic_escapeOpen c))
      = (↑(bottcherCoord c) : Germ (𝓟 (escapeOpen c)) ℂ) ^ 2
  rw [Germ.coe_compTendsto, ← Germ.coe_pow, Germ.coe_eq, eventuallyEq_principal]
  intro z hz
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  simp only [Function.comp_apply, Pi.pow_apply]
  exact bottcherCoord_quadratic hc hz2

/-- **`τ(φ_c) = φ_c²` (PROVED — the functional equation in `meroField`).** The Mahler operator sends the
genuine Böttcher coordinate `phiMero` to its square: `phiMero = algebraMap(phiAnalytic)`, `IsLocalization.map_eq`
reduces `τ` to `precompAnalytic`, and `precompAnalytic_phiAnalytic` is the germ-level functional equation.
This is the `τ φ = φ²` hypothesis of `carrier_norm_relation`. -/
theorem mahlerTau_phiMero :
    haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
      (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
    mahlerTau c (phiMero c (Set.Subset.refl (escapeOpen c)))
      = (phiMero c (Set.Subset.refl (escapeOpen c))) ^ 2 := by
  haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
    (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
  rw [phiMero]
  unfold mahlerTau
  rw [IsLocalization.map_eq, precompAnalytic_phiAnalytic, map_pow]

/-- **The φ_c norm-descent, fully assembled (PROVED).** With the carrier instances in scope
(`isDomain_analyticSubring` and `Algebra (RatFunc ℂ) (meroField (escapeOpen c))` via `ratfuncToMero`),
if the Böttcher coordinate `phiMero` is **algebraic over `ℂ(z)`** with nonconstant minimal polynomial
`m` and `m(Y), m(−Y)` coprime, then its norm `m.coeff 0` satisfies `mahlerHom(m.coeff 0)=s·(m.coeff 0)²`.
This is `carrier_norm_relation` instantiated at the concrete carrier `(meroField, τ=mahlerTau, hcompat,
τφ_c=φ_c²)` — a one-line instantiation now that all carrier pieces are built. With `s` a sign,
`mahler_eq_sq_imp_const` forces the norm constant; closing the full coupled system past norm-constant is
the genuine Nishioka core. -/
theorem phiMero_norm_relation
    [Algebra (RatFunc ℂ) (meroField (escapeOpen c))]
    (halg : (algebraMap (RatFunc ℂ) (meroField (escapeOpen c)))
      = ratfuncToMero (escapeOpen c) (isOpen_escapeOpen c) (isPreconnected_escapeOpen c)
        (escapeOpen_nonempty c) (escapeOpen_infinite c))
    (hint : IsIntegral (RatFunc ℂ) (phiMero c (Set.Subset.refl (escapeOpen c))))
    (hdeg : 0 < (minpoly (RatFunc ℂ) (phiMero c (Set.Subset.refl (escapeOpen c)))).natDegree)
    (hcop : IsCoprime (minpoly (RatFunc ℂ) (phiMero c (Set.Subset.refl (escapeOpen c))))
      ((minpoly (RatFunc ℂ) (phiMero c (Set.Subset.refl (escapeOpen c)))).comp (-X))) :
    ∃ s : RatFunc ℂ, mahlerHom c
      ((minpoly (RatFunc ℂ) (phiMero c (Set.Subset.refl (escapeOpen c)))).coeff 0)
      = s * ((minpoly (RatFunc ℂ) (phiMero c (Set.Subset.refl (escapeOpen c)))).coeff 0) ^ 2 := by
  haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
    (isPreconnected_escapeOpen c) (escapeOpen_nonempty c)
  refine carrier_norm_relation (mahlerTau c) (fun k => ?_) hint (mahlerTau_phiMero c) hdeg hcop
  rw [halg]
  exact mahlerTau_hcompat c k

/-- **Asymptotic factorization of `φ_c` (PROVED).** On the escape region, `φ_c(z) = z·exp(δ(z))` where
`δ = bottcherLog − log z` has `‖δ‖ ≤ 2‖c‖/‖z‖² → 0` (`norm_bottcherLog_sub_log_le`). So `φ_c(z)/z =
exp δ → 1` as `‖z‖→∞` — `φ_c` has a simple pole at `∞` with residue-leading term `z`. This is the
asymptotic input that forces `deg b₁ = 1` in the n=2 case (`b₁ = −(φ_c + β/φ_c) ~ −z`), which combined
with `candidate_forces_exceptional` closes n=2 for nonexceptional `c`. -/
theorem bottcherCoord_eq_z_mul_exp {c z : ℂ} (hz : z ∈ escapeOpen c) :
    bottcherCoord c z = z * Complex.exp (bottcherLog c z - Complex.log z) := by
  obtain ⟨_, hz2⟩ := mem_escapeOpen_regime hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz2; linarith
  rw [bottcherCoord, Complex.exp_sub, Complex.exp_log hz0, mul_comm z,
      div_mul_cancel₀ _ hz0]

/-- **`φ_c(t)/t → 1` along the real ray (PROVED).** As `t → +∞`, `φ_c(t)/t = exp(δ(t))` with
`‖δ(t)‖ ≤ 2‖c‖/t² → 0`, so `φ_c(t)/t → 1`. This is the precise asymptotic (`φ_c` simple pole at `∞`,
leading coefficient `1`) that forces `deg b₁ = 1` in the n=2 case. -/
theorem bottcherCoord_div_id_tendsto_one (c : ℂ) :
    Filter.Tendsto (fun t : ℝ => bottcherCoord c (t : ℂ) / (t : ℂ)) Filter.atTop (nhds 1) := by
  have hδ : Filter.Tendsto
      (fun t : ℝ => bottcherLog c (t : ℂ) - Complex.log (t : ℂ)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => 2 * ‖c‖ / t ^ 2) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop (max 2 ‖c‖)] with t ht
      have hc : ‖c‖ ≤ ‖(t : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by have := le_max_left 2 ‖c‖; linarith)]
        exact le_of_lt (lt_of_le_of_lt (le_max_right 2 ‖c‖) ht)
      have h2 : 2 < ‖(t : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by have := le_max_left 2 ‖c‖; linarith)]
        exact lt_of_le_of_lt (le_max_left 2 ‖c‖) ht
      simpa using norm_bottcherLog_sub_log_le hc h2
    · have : Filter.Tendsto (fun t : ℝ => 2 * ‖c‖ / t ^ 2) Filter.atTop (nhds 0) := by
        simpa using (tendsto_const_nhds (x := 2 * ‖c‖)).div_atTop
          (Filter.tendsto_pow_atTop (by norm_num))
      simpa using this
  have hexp : Filter.Tendsto
      (fun t : ℝ => Complex.exp (bottcherLog c (t : ℂ) - Complex.log (t : ℂ)))
      Filter.atTop (nhds 1) := by
    have := (Complex.continuous_exp.tendsto 0).comp hδ
    simpa using this
  refine hexp.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 2 ‖c‖)] with t ht
  have hmem : (t : ℂ) ∈ escapeOpen c := by
    show max 2 ‖c‖ < ‖(t : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := le_max_left 2 ‖c‖; linarith)]; exact ht
  have ht0 : (t : ℂ) ≠ 0 := by
    have : (0 : ℝ) < t := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left 2 ‖c‖)) ht
    exact_mod_cast ne_of_gt this
  rw [bottcherCoord_eq_z_mul_exp hmem, mul_comm, mul_div_assoc, div_self ht0, mul_one]

end MahlerPolynomial
