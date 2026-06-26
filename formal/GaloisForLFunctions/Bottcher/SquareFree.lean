/-
# Böttcher tower — `bottcherCoord` germ is not a square in the meromorphic field

The last Kummer input: `a` (the Böttcher germ in `meroField (escapeOpen c)`) is **not a square**
(`∀ b, b² ≠ a`), which `kummer_irreducible` (Capelli, `p = 2`) turns into `Irreducible (X^{2ᵏ} − C a)`
— the per-depth irreducibility `q62_disconnected_kummer` consumes.

Route (monodromy, non-circular): if `b² = a` in `meroField`, write `b = p/q` (`IsFractionRing`),
clear denominators to `fp² = bottcherCoord·fq²` on the connected exterior `escapeOpen c`. Both `fp, fq`
are analytic and `≢ 0`, so their zeros are countable (`analyticOnNhd_zeros_countable`); pick an avoiding
radius `R` (`exists_radius_avoiding_zeros`) where `h := fp/fq` is analytic, non-vanishing, and `h² =
bottcherCoord` on a *neighbourhood of the circle* `C(0,R)`. The sign-monodromy obstruction on that
circle (`no_analytic_sqrt_bottcher_circle`, the circle-local form of `no_analytic_sqrt_bottcher'`) gives
`False`. The exterior being non-simply-connected (`isConnected_escapeOpen`, it wraps the origin) is what
makes the obstruction live — a simply-connected `deepBall` would instead admit the root.
-/
import GaloisForLFunctions.Bottcher.NonSquare
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.Bottcher.ZeroSet
import GaloisForLFunctions.Bottcher.Q62Assembly
import GaloisForLFunctions.Bottcher.KummerDeck

open Complex Metric MeasureTheory Filter

namespace Bottcher

/-! ## The exterior carrier is connected (and not simply connected) -/

/-- **The exterior `{z | r < ‖z‖}` of a disk in `ℂ` is connected** (`0 ≤ r`). Image of the connected
product `(r,∞) × 𝕊¹` under the polar map `(t,u) ↦ t·u`. The unit circle is connected as the continuous
image of `ℝ` under `circleMap 0 1`. -/
theorem isConnected_setOf_lt_norm {r : ℝ} (hr : 0 ≤ r) :
    IsConnected {z : ℂ | r < ‖z‖} := by
  have hsphere : IsConnected (Metric.sphere (0 : ℂ) 1) := by
    have hrange : Set.range (circleMap (0 : ℂ) 1) = Metric.sphere 0 1 := by
      rw [range_circleMap, abs_one]
    rw [← hrange]; exact isConnected_range (continuous_circleMap 0 1)
  have hprod : IsConnected ((Set.Ioi r) ×ˢ Metric.sphere (0 : ℂ) 1) := isConnected_Ioi.prod hsphere
  have hcont : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  have himg := hprod.image _ hcont.continuousOn
  have hset : (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' ((Set.Ioi r) ×ˢ Metric.sphere (0 : ℂ) 1)
      = {z : ℂ | r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      rw [Set.mem_setOf_eq, norm_mul, Complex.norm_real]
      rw [mem_sphere_zero_iff_norm] at hu
      rw [hu, mul_one, Real.norm_of_nonneg (le_of_lt (lt_of_le_of_lt hr (Set.mem_Ioi.mp ht)))]
      exact Set.mem_Ioi.mp ht
    · intro hz
      have hznorm : (0 : ℝ) < ‖z‖ := lt_of_le_of_lt hr hz
      have hzne : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hznorm
      refine ⟨⟨‖z‖, z / (‖z‖ : ℂ)⟩, ⟨hz, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real,
          Real.norm_of_nonneg hznorm.le, div_self (ne_of_gt hznorm)]
      · show (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z
        field_simp
  rw [← hset]; exact himg

/-- **The Böttcher escape exterior `escapeOpen c` is connected.** Specialization of
`isConnected_setOf_lt_norm` (`max 2 ‖c‖ ≥ 0`). The connected, non-simply-connected carrier the germ
field and `analyticOnNhd_zeros_countable` need. -/
theorem isConnected_escapeOpen (c : ℂ) : IsConnected (escapeOpen c) :=
  isConnected_setOf_lt_norm (le_trans (by norm_num) (le_max_left 2 ‖c‖))

/-! ## Circle-local sign-monodromy non-squareness -/

/-- **No analytic square root of an odd-period function on a neighbourhood of a circle.** Abstract
sign-monodromy core: if `g` is non-vanishing on an open `A` containing the circle `C(0,R)` with
*odd period* `∮_{C(0,R)} d log g = 2πi`, then `g` has no analytic square root on `A` (`h² = g`). It is
enough for `h` to be analytic near the circle — `h` need not extend, which is what lets the germ
extraction use the *meromorphic* ratio `h = fp/fq`. Proof: along the loop the period of
`d log(h²) = d log g` is both `2πi` and `2·∮ d log h` with `∮ d log h ∈ 2πiℤ` (closed-loop FTC),
contradiction via `not_square_of_period_ftc`. This is the interface the cover assembly calls with
`g = φ_{c₁}∘f^[k]` (odd period `2πi` on the dyadic cover, where `φ_{c₁}` has fractional period
`2πi/2ᵏ`); `no_analytic_sqrt_bottcher_circle` is the `g = bottcherCoord c` instance. -/
theorem no_analytic_sqrt_of_odd_period {R : ℝ}
    {A : Set ℂ} (hAo : IsOpen A) (hcirc : ∀ θ : ℝ, circleMap 0 R θ ∈ A)
    {g h : ℂ → ℂ}
    (hperiod : (∮ z in C(0, R), logDeriv g z) = 2 * (Real.pi : ℂ) * Complex.I)
    (hgne : ∀ z ∈ A, g z ≠ 0)
    (hh : AnalyticOnNhd ℂ h A)
    (hsq : Set.EqOn (fun z => (h z) ^ 2) g A) :
    False := by
  have hγcont : Continuous (circleMap 0 R) := continuous_circleMap 0 R
  have hmem : ∀ θ : ℝ, circleMap 0 R θ ∈ A := hcirc
  have hne : ∀ θ : ℝ, h (circleMap 0 R θ) ≠ 0 := by
    intro θ hz0
    have he : (h (circleMap 0 R θ)) ^ 2 = g (circleMap 0 R θ) := hsq (hmem θ)
    rw [hz0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
    exact hgne _ (hmem θ) he.symm
  have hderivφ : ∀ θ, deriv (fun t => h (circleMap 0 R t)) θ
      = deriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ := fun θ =>
    ((hh (circleMap 0 R θ) (hmem θ)).differentiableAt.hasDerivAt.comp θ
      (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt).deriv
  have hcont_dh : Continuous (fun θ => deriv h (circleMap 0 R θ)) :=
    (hh.deriv.continuousOn).comp_continuous hγcont hmem
  have hcont_h : Continuous (fun θ => h (circleMap 0 R θ)) :=
    (hh.continuousOn).comp_continuous hγcont hmem
  have hcont_dγ : Continuous (fun θ => deriv (circleMap 0 R) θ) := by
    have : (fun θ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I :=
      funext fun θ => (hasDerivAt_circleMap 0 R θ).deriv
    rw [this]; exact hγcont.mul continuous_const
  have hgcont : Continuous
      (fun θ => deriv (fun t => h (circleMap 0 R t)) θ / h (circleMap 0 R θ)) := by
    have heq : (fun θ => deriv (fun t => h (circleMap 0 R t)) θ / h (circleMap 0 R θ))
        = fun θ => deriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ / h (circleMap 0 R θ) :=
      funext fun θ => by rw [hderivφ θ]
    rw [heq]; exact (hcont_dh.mul hcont_dγ).div hcont_h hne
  -- single-valued log of `h ∘ circleMap` along the loop, via the 1-D FTC
  set L : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u,
      deriv (fun s => h (circleMap 0 R s)) t / h (circleMap 0 R t) with hLdef
  have hL : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      HasDerivAt L (deriv (fun t => h (circleMap 0 R t)) θ / h (circleMap 0 R θ)) θ := by
    intro θ _
    exact intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable 0 θ)
      hgcont.stronglyMeasurable.stronglyMeasurableAtFilter hgcont.continuousAt
  -- closed-loop data
  have hγclosed : circleMap 0 R (2 * Real.pi) = circleMap 0 R 0 := by
    simpa using (periodic_circleMap 0 R) 0
  have hγd : ∀ θ, HasDerivAt (circleMap 0 R) (deriv (circleMap 0 R) θ) θ :=
    fun θ => (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt
  have hhd : ∀ θ, HasDerivAt h (deriv h (circleMap 0 R θ)) (circleMap 0 R θ) :=
    fun θ => (hh (circleMap 0 R θ) (hmem θ)).differentiableAt.hasDerivAt
  have hφd : ∀ θ, HasDerivAt (fun t => h (circleMap 0 R t))
      (deriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ) θ :=
    fun θ => (hhd θ).comp θ (hγd θ)
  have hcontinuity : Continuous
      (fun θ => logDeriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ) := by
    have heq : (fun θ => logDeriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ)
        = fun θ => deriv h (circleMap 0 R θ) / h (circleMap 0 R θ) * deriv (circleMap 0 R) θ := by
      funext θ; rw [logDeriv_apply]
    rw [heq]; exact (hcont_dh.div hcont_h hne).mul hcont_dγ
  have hbase : (∮ z in C(0, R), logDeriv g z) = 2 * (Real.pi : ℂ) * Complex.I := hperiod
  have hlogcong : ∀ θ : ℝ,
      logDeriv g (circleMap 0 R θ) = logDeriv (fun w => (h w) ^ 2) (circleMap 0 R θ) := by
    intro θ
    have heq : g =ᶠ[nhds (circleMap 0 R θ)] (fun w => (h w) ^ 2) :=
      Filter.eventuallyEq_of_mem (hAo.mem_nhds (hmem θ)) (fun w hw => (hsq hw).symm)
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.eq_of_nhds]
  have hcong : (∮ z in C(0, R), logDeriv g z)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          logDeriv (fun w => (h w) ^ 2) (circleMap 0 R θ) * deriv (circleMap 0 R) θ := by
    show (∫ θ in (0 : ℝ)..(2 * Real.pi),
            deriv (circleMap 0 R) θ • logDeriv g (circleMap 0 R θ))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi),
            logDeriv (fun w => (h w) ^ 2) (circleMap 0 R θ) * deriv (circleMap 0 R) θ
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [hlogcong θ, smul_eq_mul, mul_comm]
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), DifferentiableAt ℂ h (circleMap 0 R θ) :=
    fun θ _ => (hh (circleMap 0 R θ) (hmem θ)).differentiableAt
  have hsq2 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        logDeriv (fun w => (h w) ^ 2) (circleMap 0 R θ) * deriv (circleMap 0 R) θ)
      = 2 * ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ :=
    pathInt_logDeriv_sq (h := h) (γ := circleMap 0 R) (γ' := deriv (circleMap 0 R)) hd
  have hL'' : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt L (logDeriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ) θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity)] at hθ
    have hd2 := hL θ hθ
    rw [hderivφ θ] at hd2
    have hval : logDeriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ
        = deriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ / h (circleMap 0 R θ) := by
      rw [logDeriv_apply]; ring
    rw [hval]; exact hd2
  have hint : IntervalIntegrable (fun θ => logDeriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ)
      volume 0 (2 * Real.pi) := hcontinuity.intervalIntegrable 0 (2 * Real.pi)
  have hI3 : (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ)
      = L (2 * Real.pi) - L 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hL'' hint
  have key : 2 * (Real.pi : ℂ) * Complex.I = 2 * (L (2 * Real.pi) - L 0) := by
    rw [← hbase, hcong, hsq2, hI3]
  have hexp1 : Complex.exp (L (2 * Real.pi) - L 0) = 1 := by
    have hratio := exp_logDeriv_antiderivative (φ := fun t => h (circleMap 0 R t)) (I := L)
      (a := 0) (b := 2 * Real.pi) Real.two_pi_pos.le
      (fun t _ => hne t) (fun t _ => (hφd t).differentiableAt.hasDerivAt) (fun t ht => hL t ht)
    rw [hratio]
    show h (circleMap 0 R (2 * Real.pi)) / h (circleMap 0 R 0) = 1
    rw [hγclosed, div_self (hne 0)]
  exact not_square_of_period_ftc key hexp1

/-- **No analytic square root of `bottcherCoord` on a neighbourhood of a deep circle.** The
`g = bottcherCoord c` instance of `no_analytic_sqrt_of_odd_period`: the period is `2πi`
(`circleIntegral_logDeriv_bottcher`) and `bottcherCoord` is non-vanishing
(`bottcherCoord_ne_zero`). Used by the germ extraction with `h = fp/fq`. -/
theorem no_analytic_sqrt_bottcher_circle {c : ℂ} {R : ℝ} (hR : max 2 ‖c‖ < R)
    {A : Set ℂ} (hAo : IsOpen A) (hcirc : ∀ θ : ℝ, circleMap 0 R θ ∈ A)
    {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h A)
    (hsq : Set.EqOn (fun z => (h z) ^ 2) (bottcherCoord c) A) :
    False :=
  no_analytic_sqrt_of_odd_period hAo hcirc
    (circleIntegral_logDeriv_bottcher hR) (fun z _ => bottcherCoord_ne_zero c z) hh hsq

/-! ## Germ extraction: the Böttcher germ is not a square in `meroField` -/

/-- A germ in `analyticSubring U` equals `0` (as a germ) iff its representative vanishes on `U`. -/
private theorem germ_eq_zero_iff_eqOn {U : Set ℂ} {f : ℂ → ℂ} :
    (Germ.coeRingHom (𝓟 U) f = (0 : Germ (𝓟 U) ℂ)) ↔ Set.EqOn f 0 U := by
  rw [show Germ.coeRingHom (𝓟 U) f = (↑f : Germ (𝓟 U) ℂ) from rfl, ← Germ.coe_zero, Germ.coe_eq]
  exact ⟨fun h z hz => Filter.eventually_principal.mp h z hz,
    fun h => Filter.eventually_principal.mpr (fun z hz => h hz)⟩

/-- **The Böttcher germ is not a square in `meroField (escapeOpen c)`.** For any `a ∈ analyticSubring`
whose germ is the genuine Böttcher coordinate, no `b ∈ meroField` squares to `algebraMap a`. This is
exactly the `∀ b, b² ≠ a` input of `kummer_irreducible` (→ `Irreducible (X^{2ᵏ} − C a)`, the per-depth
irreducibility `q62_disconnected_kummer` consumes). Proof: clear denominators on `b = p/q` to
`fp² = bottcherCoord·fq²` on the connected exterior; pick a circle avoiding the (countable) zeros of
`fp·fq`; then `h = fp/fq` is an analytic square root of `bottcherCoord` near that circle — impossible by
the sign-monodromy `no_analytic_sqrt_bottcher_circle`. -/
theorem bottcherGerm_not_isSquare (c : ℂ)
    (a : analyticSubring (escapeOpen c))
    (hae : (Germ.coeRingHom (𝓟 (escapeOpen c)) (bottcherCoord c)) = (a : Germ (𝓟 (escapeOpen c)) ℂ)) :
    haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
      (isConnected_escapeOpen c).isPreconnected (isConnected_escapeOpen c).nonempty
    ∀ b : meroField (escapeOpen c),
      b ^ 2 ≠ algebraMap (analyticSubring (escapeOpen c)) (meroField (escapeOpen c)) a := by
  haveI hdom := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
    (isConnected_escapeOpen c).isPreconnected (isConnected_escapeOpen c).nonempty
  intro b hbsq
  -- write `b = algebraMap p / algebraMap q`, `q` a non-zero-divisor
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := analyticSubring (escapeOpen c)) b
  have hqunit : IsUnit (algebraMap (analyticSubring (escapeOpen c)) (meroField (escapeOpen c)) q) :=
    IsLocalization.map_units (meroField (escapeOpen c)) ⟨q, hq⟩
  have hqne : algebraMap (analyticSubring (escapeOpen c)) (meroField (escapeOpen c)) q ≠ 0 :=
    hqunit.ne_zero
  have hq0 : q ≠ 0 := fun h => hqne (by rw [h, map_zero])
  -- clear denominators: `p² = a·q²` in `analyticSubring (escapeOpen c)`
  rw [← hpq, div_pow, div_eq_iff (pow_ne_zero 2 hqne)] at hbsq
  simp only [← map_pow, ← map_mul] at hbsq
  have hpaq : p ^ 2 = a * q ^ 2 :=
    IsFractionRing.injective (analyticSubring (escapeOpen c)) (meroField (escapeOpen c)) hbsq
  -- `p ≠ 0` (else `a·q² = 0` with `a, q ≠ 0` in a domain)
  have ha0 : a ≠ 0 := by
    intro h
    have hz0 : (Germ.coeRingHom (𝓟 (escapeOpen c)) (bottcherCoord c))
        = (0 : Germ (𝓟 (escapeOpen c)) ℂ) := by rw [hae, h, ZeroMemClass.coe_zero]
    rw [germ_eq_zero_iff_eqOn] at hz0
    exact bottcherCoord_ne_zero c _ (hz0 (isConnected_escapeOpen c).nonempty.choose_spec)
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hpaq
    exact (mul_ne_zero ha0 (pow_ne_zero 2 hq0)) (by rw [← hpaq]; ring)
  -- representatives
  obtain ⟨fp, hfp, hfpe⟩ := p.2
  obtain ⟨fq, hfq, hfqe⟩ := q.2
  -- germ equation `↑(fp²) = ↑(bottcherCoord·fq²)` ⟹ `EqOn` on `escapeOpen c`
  have hval : (p : Germ (𝓟 (escapeOpen c)) ℂ) ^ 2
      = (a : Germ (𝓟 (escapeOpen c)) ℂ) * (q : Germ (𝓟 (escapeOpen c)) ℂ) ^ 2 := by
    have h := congrArg (fun x : analyticSubring (escapeOpen c) => (x : Germ (𝓟 (escapeOpen c)) ℂ)) hpaq
    simpa using h
  rw [← hae, ← hfpe, ← hfqe, ← map_pow, ← map_pow, ← map_mul] at hval
  have hEqOn : ∀ z ∈ escapeOpen c, fp z ^ 2 = bottcherCoord c z * fq z ^ 2 := by
    have hcoeeq : ((fp ^ 2 : ℂ → ℂ) : Germ (𝓟 (escapeOpen c)) ℂ)
        = ((bottcherCoord c * fq ^ 2 : ℂ → ℂ) : Germ (𝓟 (escapeOpen c)) ℂ) := hval
    rw [Germ.coe_eq] at hcoeeq
    intro z hz
    have := Filter.eventually_principal.mp hcoeeq z hz
    simpa [Pi.pow_apply, Pi.mul_apply] using this
  -- `fp·fq ≢ 0` on `escapeOpen c`: a witness with `fp w₀·fq w₀ ≠ 0`
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp0 hq0
  have hgerm_pq :
      (Germ.coeRingHom (𝓟 (escapeOpen c)) (fun z => fp z * fq z)) ≠ (0 : Germ (𝓟 (escapeOpen c)) ℂ) := by
    have hcoe : (Germ.coeRingHom (𝓟 (escapeOpen c)) (fun z => fp z * fq z))
        = ((p * q : analyticSubring (escapeOpen c)) : Germ (𝓟 (escapeOpen c)) ℂ) := by
      rw [show (fun z => fp z * fq z) = (fun z => fp z) * (fun z => fq z) from rfl, map_mul,
        hfpe, hfqe, MulMemClass.coe_mul]
    rw [hcoe]
    intro h
    apply hpq0
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact h
  obtain ⟨w₀, hw₀U, hw₀ne⟩ : ∃ z ∈ escapeOpen c, fp z * fq z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hgerm_pq (germ_eq_zero_iff_eqOn.mpr (fun z hz => by simp [hcon z hz]))
  -- avoiding radius `R` for `fp·fq`, then the near-circle analytic square root `h = fp/fq`
  obtain ⟨R, hRmem, hRavoid⟩ := exists_radius_avoiding_zeros
    (f := fun z => fp z * fq z) (U := escapeOpen c) (hfp.mul hfq)
    (isConnected_escapeOpen c).isPreconnected hw₀U hw₀ne
    (a := max 2 ‖c‖) (b := max 2 ‖c‖ + 1) (by linarith)
  have hRgt : max 2 ‖c‖ < R := hRmem.1
  have hRpos : 0 < R := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left 2 ‖c‖)) hRgt
  set A : Set ℂ := {z | z ∈ escapeOpen c ∧ fp z ≠ 0 ∧ fq z ≠ 0} with hAdef
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, hzfp, hzfq⟩
    have hUnhds : escapeOpen c ∈ nhds z := (isOpen_escapeOpen c).mem_nhds hzU
    have h1 : {w | fp w ≠ 0} ∈ nhds z :=
      (hfp z hzU).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hzfp)
    have h2 : {w | fq w ≠ 0} ∈ nhds z :=
      (hfq z hzU).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hzfq)
    filter_upwards [hUnhds, h1, h2] with w hw1 hw2 hw3
    exact ⟨hw1, hw2, hw3⟩
  have hcirc : ∀ θ : ℝ, circleMap 0 R θ ∈ A := by
    intro θ
    have hnorm : ‖circleMap 0 R θ‖ = R :=
      mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere 0 hRpos.le θ)
    have hmemU : circleMap 0 R θ ∈ escapeOpen c := by
      show max 2 ‖c‖ < ‖circleMap 0 R θ‖
      rw [hnorm]; exact hRgt
    have hpqne := hRavoid (circleMap 0 R θ) hmemU hnorm
    exact ⟨hmemU, left_ne_zero_of_mul hpqne, right_ne_zero_of_mul hpqne⟩
  have hhdiv : AnalyticOnNhd ℂ (fun z => fp z / fq z) A :=
    (hfp.mono (fun z hz => hz.1)).div (hfq.mono (fun z hz => hz.1)) (fun z hz => hz.2.2)
  have hsqA : Set.EqOn (fun z => (fp z / fq z) ^ 2) (bottcherCoord c) A := by
    intro z hz
    have hfqz : fq z ≠ 0 := hz.2.2
    have heq := hEqOn z hz.1
    show (fp z / fq z) ^ 2 = bottcherCoord c z
    rw [div_pow, heq, mul_div_assoc, div_self (pow_ne_zero 2 hfqz), mul_one]
  exact no_analytic_sqrt_bottcher_circle hRgt hAo hcirc hhdiv hsqA

/-- **`X^{2ᵏ} − C φ_c` is irreducible over `meroField (escapeOpen c)`** (`k ≥ 1`). The Capelli `p = 2`
collapse: over a `ℂ`-containing field `−1` is a square, so non-squareness of the radicand alone
(`bottcherGerm_not_isSquare`) gives irreducibility at every dyadic level (`kummer_irreducible`). This is
exactly the `Irreducible (X^{2ᵏ} − C a)` clause of the `inputs` tuple of `q62_disconnected_kummer` —
the per-depth Kummer cover field is a genuine degree-`2ᵏ` extension, with the Böttcher coordinate as a
primitive `2ᵏ`-th root of `φ_c∘f^[k] = φ_c^{2ᵏ}` (`bottcherCoord_iterate`). -/
theorem bottcher_X_pow_sub_C_irreducible (c : ℂ)
    (a : analyticSubring (escapeOpen c))
    (hae : (Germ.coeRingHom (𝓟 (escapeOpen c)) (bottcherCoord c)) = (a : Germ (𝓟 (escapeOpen c)) ℂ))
    (k : ℕ) (hk : 1 ≤ k) :
    haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
      (isConnected_escapeOpen c).isPreconnected (isConnected_escapeOpen c).nonempty
    Irreducible (Polynomial.X ^ (2 ^ k)
      - Polynomial.C (algebraMap (analyticSubring (escapeOpen c)) (meroField (escapeOpen c)) a)) := by
  haveI := isDomain_analyticSubring (escapeOpen c) (isOpen_escapeOpen c)
    (isConnected_escapeOpen c).isPreconnected (isConnected_escapeOpen c).nonempty
  refine kummer_irreducible ?_ _ (bottcherGerm_not_isSquare c a hae) k hk
  -- `−1` is a square in `meroField`: the constant germ of `Complex.I`
  refine ⟨algebraMap (analyticSubring (escapeOpen c)) (meroField (escapeOpen c))
    (constToAnalytic (escapeOpen c) Complex.I), ?_⟩
  have h1 : (constToAnalytic (escapeOpen c) Complex.I) ^ 2
      = constToAnalytic (escapeOpen c) (-1 : ℂ) := by rw [← map_pow, Complex.I_sq]
  rw [← map_pow, h1, map_neg, map_one, map_neg, map_one]

end Bottcher
