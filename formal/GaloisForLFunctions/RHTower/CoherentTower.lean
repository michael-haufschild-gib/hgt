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

/-- A coherent tower level is nonzero exactly when the base function is nonzero at
the same point.  Coherence cannot create or remove zeros on the tower domain. -/
theorem CoherentTower.level_ne_zero_iff {f : ℂ → ℂ} {U : Set ℂ}
    (T : CoherentTower f U) (k : ℕ) {s : ℂ} (hs : s ∈ U) :
    T.level k s ≠ 0 ↔ f s ≠ 0 := by
  constructor
  · intro hlev
    rw [← T.pow_eq k s hs]
    exact pow_ne_zero _ hlev
  · intro hf hzero
    apply hf
    have hpow := T.pow_eq k s hs
    rw [hzero] at hpow
    simpa [pow_ne_zero k two_ne_zero] using hpow.symm

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

/-- Levelwise dyadic roots already force nonvanishing on any open preconnected region.
Coherence is not needed for this obstruction direction: if analytic `2^k`-th roots
exist for every finite level, then any zero order would be a positive finite natural
divisible by every `2^k`, which is impossible. -/
theorem nonvanishing_of_exists_roots_all_two_powers_preconnected
    {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩpc : IsPreconnected Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    ∀ s ∈ Ω, f s ≠ 0 := by
  intro ρ hρ hρ0
  have hord : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    have hev0 : f =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩpc hρ hev0
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

/-- Levelwise dyadic roots force nonvanishing on a convex region.  This is the
convex-facing compatibility form of the preconnected obstruction theorem. -/
theorem nonvanishing_of_exists_roots_all_two_powers {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    ∀ s ∈ Ω, f s ≠ 0 :=
  nonvanishing_of_exists_roots_all_two_powers_preconnected hΩo hΩc.isPreconnected
    hz₀ hf hf0 hroots

/-- Independent dyadic roots on an open simply connected preconnected region assemble
to one coherent tower.  Convexity is not part of the assembly mechanism. -/
theorem coherentTower_of_exists_roots_all_two_powers_preconnected
    {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩsc : IsSimplyConnected Ω) (hΩpc : IsPreconnected Ω)
    (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω) (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧
      ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    Nonempty (CoherentTower f Ω) := by
  have hnz : ∀ s ∈ Ω, f s ≠ 0 :=
    nonvanishing_of_exists_roots_all_two_powers_preconnected
      hΩo hΩpc hz₀ hf hf0 hroots
  exact (coherentTower_iff_nonvanishing hΩo hΩsc hΩpc hf hz₀ hf0).2 hnz

/-- Independent dyadic roots at every finite level assemble to a coherent Kummer tower.
The proof first uses order divisibility to remove the divisor obstruction, then invokes
the logarithmic coherent-tower construction. -/
theorem coherentTower_of_exists_roots_all_two_powers {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0)
    (hroots : ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = f s) :
    Nonempty (CoherentTower f Ω) :=
  coherentTower_of_exists_roots_all_two_powers_preconnected hΩo
    (isSimplyConnected_of_convex hΩc ⟨z₀, hz₀⟩) hΩc.isPreconnected hz₀ hf hf0 hroots

/-- On open simply connected preconnected regions, coherent towers are equivalent
to having analytic dyadic roots at every finite level. -/
theorem coherentTower_iff_exists_roots_all_two_powers_preconnected
    {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ}
    (hΩo : IsOpen Ω) (hΩsc : IsSimplyConnected Ω) (hΩpc : IsPreconnected Ω)
    (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω) (hf0 : f z₀ ≠ 0) :
    Nonempty (CoherentTower f Ω) ↔
      ∀ k : ℕ, ∃ g, AnalyticOnNhd ℂ g Ω ∧
        ∀ s ∈ Ω, g s ^ (2 ^ k) = f s := by
  constructor
  · rintro ⟨T⟩ k
    exact ⟨T.level k, T.analytic k, T.pow_eq k⟩
  · exact coherentTower_of_exists_roots_all_two_powers_preconnected
      hΩo hΩsc hΩpc hz₀ hf hf0

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

namespace RHTower

open Complex Filter Set

/-- A coherent dyadic Kummer tower is equivalent to the all-level divisor constraint.
The forward direction reads divisibility from the tower levels; the reverse direction
says a positive finite zero order cannot be divisible by every `2^k`, so the U0
logarithmic construction supplies the coherent tower from zero-freeness. -/
theorem coherentTower_iff_orders_dvd_all_two_powers {f : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUsc : IsSimplyConnected U) (hUpc : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf0 : f z₀ ≠ 0) :
    Nonempty (CoherentTower f U) ↔
      ∀ k : ℕ, ∀ ρ ∈ U, f ρ = 0 → ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt f ρ := by
  constructor
  · rintro ⟨T⟩ k ρ hρ _
    exact root_orders_dvd hUo (T.analytic k) (T.pow_eq k) hρ
  · intro hdiv
    have hnz : ∀ ρ ∈ U, f ρ ≠ 0 := by
      intro ρ hρ hρ0
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
        have hthis := hdiv k ρ hρ hρ0
        rw [← hm] at hthis
        exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hthis
      have hm0 : m = 0 := by
        by_contra hm0
        have h2 : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd m)
        have h3 : m < 2 ^ m := Nat.lt_pow_self (by norm_num)
        omega
      have hne : analyticOrderAt f ρ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf ρ hρ, hρ0⟩
      rw [← hm, hm0] at hne
      exact hne rfl
    exact (coherentTower_iff_nonvanishing hUo hUsc hUpc hf hz₀ hf0).2 hnz

end RHTower

namespace RHTower

open Complex Filter Set Metric Bottcher
open U0MStepBranch U0PhiMStep U0MeroCarrier

/-- **The concrete U0 Kummer tower as an RHTower coherent tower.**  For every viable
U0 parameter, the U0 `psiN` tower can be consumed through the generic `CoherentTower`
API, while every coherent level retains its meromorphic `NoRelation` certificate against
`u₀`. -/
theorem u0_coherentTower_with_noRelation_of_viable {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) :
    ∃ (r : ℝ) (N : ℕ) (hr : 1 < r) (T : CoherentTower (psiN b N) (ball (0 : ℂ) r)),
      (∀ k z, T.level k z ≠ 0) ∧
      (∀ k,
        letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
          (annMB_nonempty hr)
        letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
          (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
            (annMB_infinite hr)).toAlgebra
        NoRelation (RatFunc ℂ)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            ⟨Germ.coeRingHom (𝓟 (annMB r)) (T.level k),
              ⟨T.level k, (T.analytic k).mono inter_subset_left, rfl⟩⟩)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            (u0AnSub annMB_subset_Ext))) := by
  obtain ⟨r, N, hr, χ, hχ, hχ0, hbase, hsq, _hpow, hrel⟩ :=
    U0KummerBranch.u0_coherent_kummer_tower hviab
  let T : CoherentTower (psiN b N) (ball (0 : ℂ) r) :=
    { level := χ
      level_zero := hbase
      analytic := hχ
      sq := hsq }
  refine ⟨r, N, hr, T, ?_, ?_⟩
  · exact hχ0
  · intro k
    exact hrel k

end RHTower
