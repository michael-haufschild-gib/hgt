/-
# Finite covers of the basin do not trivialise the Böttcher monodromy

Let `c ∉ M` and let `π : Y → Ω_c` be a covering map of the basin of infinity `Ω_c = ℂ ∖ K_c` with
finite fibres.

* **Fibres.** Over an evenly covered neighbourhood all fibres are homeomorphic, so the fibre
  cardinality is locally constant, hence constant on the connected basin; call it `D`.
* **Laps.** Lift a basin loop `ℓ` along the whole real line (`ℝ` is simply connected) from a point
  of the fibre over `ℓ(0)`.  The `D + 1` lap endpoints `Λ(2πk)` lie in a fibre with `D` points, so
  two coincide; after a shift the lift `Λ` is `2πm`-periodic for some `1 ≤ m ≤ D`.
* **No single-valued branch.**  A single-valued nonvanishing `F` on `Y` that is locally a branch of
  `φ_c ∘ π` (a local solution of `g' = ω g` pulled back by `π`) gives a continuation `F ∘ Λ` along
  `ℓ`, so `exp(m ∮_ℓ ω) = 1`.  For a loop with period `2πi / 2ⁿ` and `2ⁿ > D` this contradicts
  `m ≤ D`.
* **Full Prüfer image survives.**  For a loop with period `2πi / 2^{n+D}`, the multiplier
  `exp(m ∮_ℓ ω)` of the closed lift of the `m`-fold loop has order `2^{n+D}/gcd(2^{n+D}, m)`,
  divisible by `2ⁿ`; its powers, the multipliers of the closed lifts of the iterated loops, contain
  every `2ⁿ`-th root of unity.  So the monodromy image of loops with closed lift to `Y` is again
  exactly the Prüfer group `μ_{2^∞}`.
-/
import GaloisForLFunctions.Bottcher.BottcherContinuation
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.CompMul

open Complex Set Filter Topology

namespace Bottcher

noncomputable section

/-! ### Fibres of a covering map -/

section Fibre

variable {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] {π : Y → X}

/-- **Nearby fibres of a covering map are equinumerous.** -/
theorem eventually_cardinalMk_fiber_eq_of_isCoveringMap (hπ : IsCoveringMap π) (x : X) :
    ∀ᶠ x' in 𝓝 x, Cardinal.mk (π ⁻¹' {x'}) = Cardinal.mk (π ⁻¹' {x}) := by
  obtain ⟨hdisc, U, hxU, hUo, hpre, H, hH⟩ := hπ x
  filter_upwards [hUo.mem_nhds hxU] with x' hx'
  exact (Cardinal.mk_congr (IsEvenlyCovered.fiberHomeomorph
    (⟨hdisc, U, hx', hUo, hpre, H, hH⟩ : IsEvenlyCovered π x' (π ⁻¹' {x}))).toEquiv).symm

/-- **The fibres of a covering map of a connected space are equinumerous.** -/
theorem cardinalMk_fiber_eq_of_isCoveringMap [PreconnectedSpace X] (hπ : IsCoveringMap π)
    (x x' : X) : Cardinal.mk (π ⁻¹' {x'}) = Cardinal.mk (π ⁻¹' {x}) :=
  congrFun (((IsLocallyConstant.iff_eventually_eq _).mpr
    (eventually_cardinalMk_fiber_eq_of_isCoveringMap hπ)).eq_const x) x'

end Fibre

/-! ### The basin and iterated loops -/

/-- The basin of infinity `Ω_c = ℂ ∖ K_c` as a topological space. -/
abbrev Basin (c : ℂ) : Type := ↥(filledJulia c)ᶜ

instance (c : ℂ) : PreconnectedSpace (Basin c) :=
  Subtype.preconnectedSpace (isPreconnected_compl_filledJulia c)

variable {c : ℂ}

/-- A basin loop as a continuous map of the whole parameter line into the basin. -/
def BasinLoop.basinPath (ℓ : BasinLoop c) : C(ℝ, Basin c) :=
  ⟨fun θ => ⟨ℓ.γ θ, ℓ.mem θ⟩, ℓ.smooth.continuous.subtype_mk _⟩

@[simp] theorem BasinLoop.basinPath_apply (ℓ : BasinLoop c) (θ : ℝ) :
    ((ℓ.basinPath θ : Basin c) : ℂ) = ℓ.γ θ := rfl

/-- The `m`-fold iterate `θ ↦ γ(mθ)` of a basin loop. -/
def BasinLoop.iterate (ℓ : BasinLoop c) (m : ℕ) : BasinLoop c where
  γ θ := ℓ.γ (m * θ)
  smooth := ℓ.smooth.comp (contDiff_const.mul contDiff_id)
  periodic θ := by
    change ℓ.γ (m * (θ + 2 * Real.pi)) = ℓ.γ (m * θ)
    rw [mul_add]
    exact ℓ.periodic.nat_mul m (m * θ)
  mem θ := ℓ.mem _

/-- The integrand `ω(γ)γ'` of a basin loop is `2π`-periodic. -/
theorem BasinLoop.periodic_integrand (ℓ : BasinLoop c) :
    Function.Periodic (fun s => greenLogDeriv c (ℓ.γ s) * deriv ℓ.γ s) (2 * Real.pi) := by
  intro s
  have hd : deriv ℓ.γ (s + 2 * Real.pi) = deriv ℓ.γ s := by
    rw [← deriv_comp_add_const]
    congr 1
    funext y
    exact ℓ.periodic y
  simp only [ℓ.periodic s, hd]

/-- **The integral of `ω` over `k` laps is `k` times the period.** -/
theorem BasinLoop.integral_nat_mul (ℓ : BasinLoop c) (k : ℕ) :
    ∫ s in (0:ℝ)..k * (2 * Real.pi), greenLogDeriv c (ℓ.γ s) * deriv ℓ.γ s = k * ℓ.period := by
  have h := ℓ.periodic_integrand.intervalIntegral_add_zsmul_eq (k : ℤ) 0
    (fun t₁ t₂ => (continuous_greenLogDeriv_path ℓ.smooth ℓ.mem).intervalIntegrable t₁ t₂)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at h
  rw [h, BasinLoop.period]

/-- **The period of the `m`-fold iterate is `m` times the period.** -/
theorem BasinLoop.period_iterate (ℓ : BasinLoop c) (m : ℕ) :
    (ℓ.iterate m).period = m * ℓ.period := by
  rw [← ℓ.integral_nat_mul m]
  set f : ℝ → ℂ := fun s => greenLogDeriv c (ℓ.γ s) * deriv ℓ.γ s
  have hint : ∀ θ, greenLogDeriv c ((ℓ.iterate m).γ θ) * deriv (ℓ.iterate m).γ θ =
      (m : ℝ) • f (m * θ) := by
    intro θ
    change greenLogDeriv c (ℓ.γ (m * θ)) * deriv (fun θ => ℓ.γ (m * θ)) θ = _
    rw [deriv_comp_mul_left (m : ℝ) ℓ.γ θ, mul_smul_comm]
  have h := intervalIntegral.smul_integral_comp_mul_left f (m : ℝ) (a := 0) (b := 2 * Real.pi)
  rw [mul_zero] at h
  rw [BasinLoop.period, ← h, ← intervalIntegral.integral_smul]
  exact intervalIntegral.integral_congr fun θ _ => hint θ

/-! ### Lifting basin loops to a finite cover -/

variable {Y : Type*} [TopologicalSpace Y] {π : Y → Basin c}

/-- A single-valued function on the cover that is locally a branch of `φ_c ∘ π`, i.e. locally
`g ∘ π` for a local solution `g` of `g' = ω g`. -/
def IsCoverBottcherBranch (π : Y → Basin c) (F : Y → ℂ) : Prop :=
  ∀ y, ∃ U : Set ℂ, IsOpen U ∧ ((π y : Basin c) : ℂ) ∈ U ∧ U ⊆ (filledJulia c)ᶜ ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ (∀ z ∈ U, deriv g z = greenLogDeriv c z * g z) ∧
      ∀ᶠ y' in 𝓝 y, F y' = g (π y')

/-- **Pull-back along a lift.**  A cover branch composed with a lift of a basin path is a
continuation along the path. -/
theorem IsCoverBottcherBranch.isBasinContinuation {F : Y → ℂ} (hF : IsCoverBottcherBranch π F)
    {γ : ℝ → ℂ} {Λ : ℝ → Y} (hΛ : Continuous Λ) (hlift : ∀ θ, ((π (Λ θ) : Basin c) : ℂ) = γ θ)
    (a b : ℝ) : IsBasinContinuation c γ a b (fun θ => F (Λ θ)) := by
  intro θ₀ _
  obtain ⟨U, hUo, hU, hUK, g, hgd, hgω, hFg⟩ := hF (Λ θ₀)
  refine ⟨U, hUo, hlift θ₀ ▸ hU, hUK, g, hgd, hgω, nhdsWithin_le_nhds ?_⟩
  filter_upwards [hΛ.continuousAt.eventually hFg] with θ hθ
  rw [hθ, hlift θ]

/-- **Uniform lap recurrence.**  For a covering of the basin with finite fibres there is a bound
`D` such that every basin loop has a lift along `ℝ` that is `2πm`-periodic for some `1 ≤ m ≤ D`. -/
theorem exists_periodic_loop_lift [Nonempty Y] (hπ : IsCoveringMap π)
    (hfin : ∀ x, (π ⁻¹' {x}).Finite) :
    ∃ D : ℕ, ∀ ℓ : BasinLoop c, ∃ (Λ : C(ℝ, Y)) (m : ℕ), 0 < m ∧ m ≤ D ∧
      (∀ θ, ((π (Λ θ) : Basin c) : ℂ) = ℓ.γ θ) ∧ Function.Periodic Λ (m * (2 * Real.pi)) := by
  obtain ⟨yst⟩ := ‹Nonempty Y›
  refine ⟨Nat.card (π ⁻¹' {π yst}), fun ℓ => ?_⟩
  set x₀ : Basin c := ℓ.basinPath 0
  have hmk := cardinalMk_fiber_eq_of_isCoveringMap hπ (π yst) x₀
  have hcard : Nat.card (π ⁻¹' {x₀}) = Nat.card (π ⁻¹' {π yst}) := by
    rw [Nat.card, Nat.card, hmk]
  obtain ⟨⟨y₀, hy₀⟩⟩ : Nonempty (π ⁻¹' {x₀}) := by
    rw [← Cardinal.mk_ne_zero_iff, hmk, Cardinal.mk_ne_zero_iff]
    exact ⟨⟨yst, rfl⟩⟩
  obtain ⟨Λ₀, ⟨hΛ₀0, hΛ₀⟩, -⟩ := hπ.existsUnique_continuousMap_lifts ℓ.basinPath 0 y₀ hy₀
  have hlift₀ : ∀ θ, π (Λ₀ θ) = ℓ.basinPath θ := fun θ => congrFun hΛ₀ θ
  have hlap : ∀ k : ℕ, π (Λ₀ (k * (2 * Real.pi))) = x₀ := fun k => by
    rw [hlift₀]
    exact Subtype.ext (ℓ.periodic.nat_mul_eq k)
  -- two lap endpoints coincide
  haveI : Finite (π ⁻¹' {x₀}) := hfin x₀
  obtain ⟨i, j, hij, hjD, heq⟩ : ∃ i j : ℕ, i < j ∧ j ≤ Nat.card (π ⁻¹' {π yst}) ∧
      Λ₀ (i * (2 * Real.pi)) = Λ₀ (j * (2 * Real.pi)) := by
    set e : Fin (Nat.card (π ⁻¹' {π yst}) + 1) → π ⁻¹' {x₀} :=
      fun k => ⟨Λ₀ ((k : ℕ) * (2 * Real.pi)), hlap k⟩
    have hni : ¬ Function.Injective e := fun hinj => by
      have := Nat.card_le_card_of_injective e hinj
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at this
      omega
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    have hval : Λ₀ ((a : ℕ) * (2 * Real.pi)) = Λ₀ ((b : ℕ) * (2 * Real.pi)) :=
      congrArg Subtype.val hab
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact ⟨a, b, h, by omega, hval⟩
    · exact ⟨b, a, h, by omega, hval.symm⟩
  -- shift the lift to the recurrent lap and use uniqueness of lifts
  set Λ : C(ℝ, Y) := Λ₀.comp ⟨fun θ => θ + i * (2 * Real.pi), by fun_prop⟩
  have hΛ : ∀ θ, π (Λ θ) = ℓ.basinPath θ := fun θ => by
    change π (Λ₀ (θ + i * (2 * Real.pi))) = _
    rw [hlift₀]
    exact Subtype.ext (ℓ.periodic.nat_mul i θ)
  refine ⟨Λ, j - i, by omega, by omega, fun θ => congrArg Subtype.val (hΛ θ), ?_⟩
  have hshift : (fun θ => Λ (θ + (j - i : ℕ) * (2 * Real.pi))) = Λ := by
    refine hπ.eq_of_comp_eq (by fun_prop) Λ.continuous (funext fun θ => ?_) 0 ?_
    · simp only [Function.comp_apply, hΛ]
      exact Subtype.ext (ℓ.periodic.nat_mul (j - i) θ)
    · change Λ₀ (0 + ((j - i : ℕ) : ℝ) * (2 * Real.pi) + i * (2 * Real.pi)) =
        Λ₀ (0 + i * (2 * Real.pi))
      rw [zero_add, zero_add, heq, Nat.cast_sub hij.le]
      congr 1
      ring
  exact fun θ => congrFun hshift θ

/-! ### Main theorems -/

/-- **No finite cover makes the Böttcher coordinate single-valued.**  For `c ∉ M` and a covering
`π : Y → Ω_c` with finite fibres, no single-valued nonvanishing function on `Y` is locally a branch
of `φ_c ∘ π`. -/
theorem not_exists_isCoverBottcherBranch (hc : Disconnected c) [Nonempty Y]
    (hπ : IsCoveringMap π) (hfin : ∀ x, (π ⁻¹' {x}).Finite) :
    ¬ ∃ F : Y → ℂ, (∀ y, F y ≠ 0) ∧ IsCoverBottcherBranch π F := by
  rintro ⟨F, hF0, hF⟩
  obtain ⟨D, hD⟩ := exists_periodic_loop_lift hπ hfin
  obtain ⟨ℓ, hℓ⟩ := exists_basinLoop_period_eq hc D 1
  obtain ⟨Λ, m, hm0, hmD, hlift, hper⟩ := hD ℓ
  have hcont := (hF.isBasinContinuation Λ.continuous hlift 0 (m * (2 * Real.pi))).eq_exp_integral_mul
    ℓ.smooth ℓ.mem (by positivity)
  rw [ℓ.integral_nat_mul m, hper.eq] at hcont
  have hone : Complex.exp ℓ.period ^ m = 1 := by
    rw [← Complex.exp_nat_mul]
    exact (mul_eq_right₀ (hF0 _)).mp hcont.symm
  have hexp : Complex.exp ℓ.period = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ D : ℕ) : ℂ)) := by
    rw [hℓ]
    congr 1
    push_cast
    ring
  have hdvd : 2 ^ D ∣ m := by
    rw [← orderOf_dyadicRoot D, ← hexp]
    exact orderOf_dvd_of_pow_eq_one hone
  have := Nat.le_of_dvd hm0 hdvd
  have := (Nat.lt_two_pow_self (n := D))
  omega

/-- **Every finite cover sees the full Prüfer monodromy.**  For `c ∉ M` and a covering
`π : Y → Ω_c` with finite fibres, the scalar monodromy of continuation of the Böttcher coordinate
around the basin loops whose lift to `Y` is closed is exactly the group of dyadic roots of unity. -/
theorem finiteCover_monodromy_image_eq_dyadicRootsOfUnity (hc : Disconnected c) [Nonempty Y]
    (hπ : IsCoveringMap π) (hfin : ∀ x, (π ⁻¹' {x}).Finite) :
    {μ : ℂ | ∃ (ℓ : BasinLoop c) (Γ : ℝ → Y) (F : ℝ → ℂ), Continuous Γ ∧
      (∀ θ, ((π (Γ θ) : Basin c) : ℂ) = ℓ.γ θ) ∧ Γ (2 * Real.pi) = Γ 0 ∧
      IsBasinContinuation c ℓ.γ 0 (2 * Real.pi) F ∧ F 0 ≠ 0 ∧ F (2 * Real.pi) = μ * F 0} =
      dyadicRootsOfUnity := by
  ext ζ
  constructor
  · rintro ⟨ℓ, -, F, -, -, -, hF, hF0, hμ⟩
    rw [← basin_monodromy_image_eq_dyadicRootsOfUnity hc]
    exact ⟨ℓ, F, hF, hF0, hμ⟩
  rintro ⟨n, hζ⟩
  obtain ⟨D, hD⟩ := exists_periodic_loop_lift hπ hfin
  obtain ⟨ℓ, hℓ⟩ := exists_basinLoop_period_eq hc (n + D) 1
  obtain ⟨Λ, m, hm0, hmD, hlift, hper⟩ := hD ℓ
  -- the multiplier of the `m`-fold loop has order divisible by `2ⁿ`
  set η := Complex.exp ℓ.period ^ m with hηdef
  have hexp : Complex.exp ℓ.period =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ (n + D) : ℕ) : ℂ)) := by
    rw [hℓ]
    congr 1
    push_cast
    ring
  have hord : orderOf (Complex.exp ℓ.period) = 2 ^ (n + D) := by
    rw [hexp, orderOf_dyadicRoot]
  have hordη : orderOf η = 2 ^ (n + D) / Nat.gcd (2 ^ (n + D)) m := by
    rw [hηdef, orderOf_pow' _ hm0.ne', hord]
  obtain ⟨v, hvle, hv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ (n + D)) m)
  have hvD : v < D := by
    have h1 : 2 ^ v ≤ m := hv ▸ Nat.le_of_dvd hm0 (Nat.gcd_dvd_right _ _)
    have h2 : m < 2 ^ D := lt_of_le_of_lt hmD Nat.lt_two_pow_self
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 h2)
  have hordη' : orderOf η = 2 ^ (n + D - v) := by
    rw [hordη, hv, Nat.pow_div hvle (by norm_num)]
  have hζη : ζ ^ orderOf η = 1 := by
    rw [hordη', show n + D - v = n + (D - v) by omega, pow_add, pow_mul, hζ, one_pow]
  haveI : NeZero (orderOf η) := ⟨by rw [hordη']; positivity⟩
  obtain ⟨r, -, hr⟩ := (IsPrimitiveRoot.orderOf η).eq_pow_of_pow_eq_one hζη
  -- the closed lift of the `m r`-fold loop
  set ℓ' := ℓ.iterate (m * r)
  obtain ⟨F, hF, hF0⟩ := exists_isBasinContinuation (c := c) ℓ'.smooth ℓ'.mem 0 (2 * Real.pi) 1
  refine ⟨ℓ', fun θ => Λ ((m * r : ℕ) * θ), F, by fun_prop, fun θ => hlift _, ?_, hF,
    by rw [hF0]; exact one_ne_zero, ?_⟩
  · change Λ (((m * r : ℕ) : ℝ) * (2 * Real.pi)) = Λ (((m * r : ℕ) : ℝ) * 0)
    rw [mul_zero, show ((m * r : ℕ) : ℝ) * (2 * Real.pi) = r * (m * (2 * Real.pi)) by
      push_cast; ring]
    exact (hper.nat_mul r).eq
  · rw [ℓ'.continuation_multiplier hF, BasinLoop.period_iterate, Complex.exp_nat_mul, pow_mul, ← hr]
