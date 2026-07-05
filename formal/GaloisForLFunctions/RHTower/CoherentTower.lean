/-
# The coherent ℤ₂-Kummer tower — existence iff nonvanishing

Arc A1d of the MWM lane (docs/drafts/rh-monodromy-weight-mismatch/): the generic packaging of
the `u0_coherent_kummer_tower` construction.  A `CoherentTower f U` has level 0 equal to `f`
and each level an analytic square root of the previous one — the whole 2-power root tower as
one pro-object, generated from a single analytic logarithm.  On a simply connected,
preconnected open set with a marked nonvanishing point, the tower exists **iff** `f` has no
zeros on `U` — the ℤ₂-branching obstruction is exactly the divisor.
-/
import GaloisForLFunctions.RHTower.RootExistence

namespace RHTower

open Complex Filter Set

/-- A coherent ℤ₂-Kummer tower over `U`: level 0 is `f`, each level an analytic square root
of the previous one. -/
structure CoherentTower (f : ℂ → ℂ) (U : Set ℂ) where
  level : ℕ → ℂ → ℂ
  level_zero : ∀ s ∈ U, level 0 s = f s
  analytic : ∀ k, AnalyticOnNhd ℂ (level k) U
  sq : ∀ k, ∀ s ∈ U, level (k + 1) s ^ 2 = level k s

/-- Level `k` of a coherent tower is a `2^k`-th root of `f`. -/
theorem CoherentTower.pow_eq {f : ℂ → ℂ} {U : Set ℂ} (T : CoherentTower f U) (k : ℕ) :
    ∀ s ∈ U, T.level k s ^ 2 ^ k = f s := by
  induction k with
  | zero =>
    intro s hs
    simpa using T.level_zero s hs
  | succ k ih =>
    intro s hs
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2, pow_mul, T.sq k s hs]
    exact ih s hs

/-- **The coherent ℤ₂-tower exists iff `f` is nonvanishing.**  The obstruction to the whole
2-power root tower of an analytic function is exactly its zero divisor. -/
theorem coherentTower_iff_nonvanishing {f : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf0 : f z₀ ≠ 0) :
    Nonempty (CoherentTower f U) ↔ ∀ s ∈ U, f s ≠ 0 := by
  constructor
  · rintro ⟨T⟩ ρ hρ hρ0
    have hord : analyticOrderAt f ρ ≠ ⊤ := by
      intro htop
      have hev0 : f =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
        filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
        simpa using hz
      exact hf0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpc hρ hev0 hz₀)
    set m : ℕ := (analyticOrderAt f ρ).toNat with hmdef
    have hm : (m : ℕ∞) = analyticOrderAt f ρ := ENat.coe_toNat hord
    have hdvd : ∀ k : ℕ, 2 ^ k ∣ m := by
      intro k
      have hdvd' : ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt f ρ :=
        root_orders_dvd hUo (T.analytic k) (T.pow_eq k) hρ
      rw [← hm] at hdvd'
      exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd'
    have hm0 : m = 0 := by
      by_contra hm0
      have h2 : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd m)
      have h3 : m < 2 ^ m := Nat.lt_pow_self (by norm_num)
      omega
    have hne : analyticOrderAt f ρ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf ρ hρ, hρ0⟩
    rw [← hm, hm0] at hne
    exact hne rfl
  · intro hnz
    have hU0 : (0 : ℂ) ∉ f '' U := by
      rintro ⟨z, hz, hfz⟩
      exact hnz z hz hfz
    obtain ⟨L, hLc, hLeq⟩ :=
      Complex.exists_continuousOn_eqOn_exp_comp hUsc hUo hf.continuousOn hU0
    have hLan : AnalyticOnNhd ℂ L U :=
      U0KummerBranch.analyticOnNhd_of_continuousOn_exp_eq hUo hLc hf (fun z hz => hLeq hz)
    have hlev : ∀ k : ℕ, AnalyticOnNhd ℂ (fun s => Complex.exp (L s / 2 ^ k)) U := by
      intro k
      have hdiff : DifferentiableOn ℂ (fun z => Complex.exp (L z / 2 ^ k)) U :=
        fun z hz =>
          (((hLan z hz).differentiableAt.div_const ((2 : ℂ) ^ k)).cexp).differentiableWithinAt
      exact hdiff.analyticOnNhd hUo
    refine ⟨⟨fun k s => Complex.exp (L s / 2 ^ k), ?_, hlev, ?_⟩⟩
    · intro s hs
      simpa using hLeq hs
    · intro k s hs
      rw [← Complex.exp_nat_mul (L s / 2 ^ (k + 1)) 2]
      congr 1
      have h2 : ((2 : ℂ)) ^ (k + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
      have h3 : ((2 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
      push_cast
      field_simp
      ring

end RHTower

namespace RHTower

open Complex Filter Set

/-- Levelwise dyadic roots already force nonvanishing.  Coherence is not needed for
this obstruction direction: if analytic `2^k`-th roots exist for every finite level,
then any zero order would be a positive finite natural divisible by every `2^k`, which
is impossible. -/
theorem nonvanishing_of_exists_roots_all_two_powers {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    ∀ s ∈ Ω, f s ≠ 0 := by
  intro ρ hρ hρ0
  have hord : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    have hev0 : f =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc.isPreconnected hρ hev0
    exact hf0 (this hz₀)
  set m : ℕ := (analyticOrderAt f ρ).toNat with hmdef
  have hm : (m : ℕ∞) = analyticOrderAt f ρ := ENat.coe_toNat hord
  have hdvd : ∀ k : ℕ, 2 ^ k ∣ m := by
    intro k
    obtain ⟨g, hgan, hgpow⟩ := hroots k
    have hdvd' : ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt f ρ :=
      root_orders_dvd hΩo hgan hgpow hρ
    rw [← hm] at hdvd'
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd'
  have hm0 : m = 0 := by
    by_contra hm0
    have h2 : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd m)
    have h3 : m < 2 ^ m := Nat.lt_pow_self (by norm_num)
    omega
  have hne : analyticOrderAt f ρ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf ρ hρ, hρ0⟩
  rw [← hm, hm0] at hne
  exact hne rfl

/-- Independent dyadic roots at every finite level assemble to a coherent Kummer tower.
The proof first uses order divisibility to remove the divisor obstruction, then invokes
the logarithmic coherent-tower construction. -/
theorem coherentTower_of_exists_roots_all_two_powers {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    Nonempty (CoherentTower f Ω) := by
  have hnz : ∀ s ∈ Ω, f s ≠ 0 :=
    nonvanishing_of_exists_roots_all_two_powers hΩo hΩc hz₀ hf hf0 hroots
  exact (coherentTower_iff_nonvanishing hΩo (isSimplyConnected_of_convex hΩc ⟨z₀, hz₀⟩)
    hΩc.isPreconnected hf hz₀ hf0).2 hnz

/-- Coherence is equivalent to having independent analytic dyadic roots at every
finite level.  The reverse direction is the divisor obstruction; the forward
direction reads the roots directly from the coherent tower levels. -/
theorem coherentTower_iff_exists_roots_all_two_powers {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0) :
    Nonempty (CoherentTower f Ω) ↔
      ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = f s := by
  constructor
  · rintro ⟨T⟩ k
    exact ⟨T.level k, T.analytic k, T.pow_eq k⟩
  · exact coherentTower_of_exists_roots_all_two_powers hΩo hΩc hz₀ hf hf0

end RHTower
