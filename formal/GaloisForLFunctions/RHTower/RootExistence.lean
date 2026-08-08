/-
# Kummer obstruction III — divisibility of orders is sufficient for analytic roots

The load-bearing Arc A theorem of the MWM lane (docs/drafts/rh-monodromy-weight-mismatch/):
on a convex open set `Ω` with a marked point where `f` does not vanish, and whose zero set is
finite in every bounded piece, an analytic `n`-th root of `f` exists **iff** every vanishing
order of `f` on `Ω` is divisible by `n` (`exists_root_iff_orders_dvd`).

Necessity is `root_orders_dvd` (KummerObstruction).  Sufficiency: peel the finitely many
zeros of a bounded convex piece (`Peeling.exists_peel`, induction), take the nonvanishing
root from the banked construction `U0KummerBranch.exists_analyticOnNhd_pow_eq`, normalise all
piece-roots at the marked point, and glue along the convex exhaustion
`Ω ∩ ball z₀ (R+1)` using root rigidity (`pow_root_unique`).
-/
import GaloisForLFunctions.HTGeometry.Peeling
import GaloisForLFunctions.U0.U0KummerBranch

namespace RHTower

open Complex Filter Set Metric

/-- Root existence when the zero set is finite: induction on the number of zeros, peeling one
zero per step. -/
theorem exists_root_of_finite {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∀ (f : ℂ → ℂ) (U : Set ℂ), IsOpen U → IsSimplyConnected U → IsPreconnected U →
      AnalyticOnNhd ℂ f U → ∀ hZ : {s ∈ U | f s = 0}.Finite, hZ.toFinset.card ≤ k →
      (∀ ρ ∈ U, f ρ = 0 → (n : ℕ∞) ∣ analyticOrderAt f ρ) →
      (∀ ρ ∈ U, analyticOrderAt f ρ ≠ ⊤) →
      ∃ g, AnalyticOnNhd ℂ g U ∧ ∀ s ∈ U, g s ^ n = f s := by
  induction k with
  | zero =>
    intro f U hUo hUsc hUpc hf hZ hcard hdvd hfin
    have hZempty : {s ∈ U | f s = 0} = ∅ := by
      have h0 : hZ.toFinset.card = 0 := Nat.le_zero.mp hcard
      simpa [Set.Finite.toFinset_eq_empty] using Finset.card_eq_zero.mp h0
    have hg0 : ∀ z ∈ U, f z ≠ 0 := by
      intro z hz hfz
      exact absurd (Set.mem_setOf.mpr ⟨hz, hfz⟩ : z ∈ {s ∈ U | f s = 0}) (by simp [hZempty])
    obtain ⟨χ, hχan, _, hχpow⟩ :=
      U0KummerBranch.exists_analyticOnNhd_pow_eq hUo hUsc hf hg0 hn.ne'
    exact ⟨χ, hχan, hχpow⟩
  | succ k ih =>
    intro f U hUo hUsc hUpc hf hZ hcard hdvd hfin
    rcases Set.eq_empty_or_nonempty {s ∈ U | f s = 0} with hZe | ⟨ρ, hρZ⟩
    · have hg0 : ∀ z ∈ U, f z ≠ 0 := by
        intro z hz hfz
        exact absurd (Set.mem_setOf.mpr ⟨hz, hfz⟩ : z ∈ {s ∈ U | f s = 0}) (by simp [hZe])
      obtain ⟨χ, hχan, _, hχpow⟩ :=
        U0KummerBranch.exists_analyticOnNhd_pow_eq hUo hUsc hf hg0 hn.ne'
      exact ⟨χ, hχan, hχpow⟩
    · obtain ⟨hρU, hρ0⟩ := hρZ
      -- the order at ρ is a finite positive multiple of n
      set m : ℕ := (analyticOrderAt f ρ).toNat with hmdef
      have hm : (m : ℕ∞) = analyticOrderAt f ρ := ENat.coe_toNat (hfin ρ hρU)
      obtain ⟨c, hc⟩ := hdvd ρ hρU hρ0
      have hc_ne : c ≠ ⊤ := by
        intro hct
        apply hfin ρ hρU
        rw [hc, hct]
        exact ENat.mul_top (by exact_mod_cast hn.ne')
      set q : ℕ := c.toNat with hqdef
      have hq : (q : ℕ∞) = c := ENat.coe_toNat hc_ne
      have hmnq : m = n * q := by
        have h1 : ((m : ℕ) : ℕ∞) = ((n * q : ℕ) : ℕ∞) := by
          rw [Nat.cast_mul, hq, ← hc]
          exact hm
        exact_mod_cast h1
      -- peel the zero at ρ
      obtain ⟨h, hhan, hhρ0, hfact, horders⟩ := exists_peel hUo hf hρU hm.symm
      -- the peeled function has one fewer zero, same divisibility, finite orders
      have hZh_eq : {s ∈ U | h s = 0} = {s ∈ U | f s = 0} \ {ρ} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hxU, hx0⟩
          have hxρ : x ≠ ρ := fun he => hhρ0 (he ▸ hx0)
          refine ⟨⟨hxU, ?_⟩, hxρ⟩
          rw [hfact x hxU, hx0, mul_zero]
        · rintro ⟨⟨hxU, hx0⟩, hxρ⟩
          refine ⟨hxU, ?_⟩
          have hne : (x - ρ) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hxρ)
          have := hfact x hxU
          rw [hx0] at this
          exact (mul_eq_zero.mp this.symm).resolve_left hne
      have hZh : {s ∈ U | h s = 0}.Finite := by
        rw [hZh_eq]; exact hZ.sdiff
      have hZh_card : hZh.toFinset.card ≤ k := by
        have hsub : hZh.toFinset = hZ.toFinset.erase ρ := by
          ext x
          simp only [Set.Finite.mem_toFinset, Finset.mem_erase, hZh_eq, Set.mem_sdiff,
            Set.mem_singleton_iff, Set.Finite.mem_toFinset]
          tauto
        have hρmem : ρ ∈ hZ.toFinset := by
          simp only [Set.Finite.mem_toFinset]
          exact ⟨hρU, hρ0⟩
        rw [hsub, Finset.card_erase_of_mem hρmem]
        omega
      have hdvd_h : ∀ σ ∈ U, h σ = 0 → (n : ℕ∞) ∣ analyticOrderAt h σ := by
        intro σ hσU hσ0
        have hσρ : σ ≠ ρ := fun he => hhρ0 (he ▸ hσ0)
        have hfσ0 : f σ = 0 := by rw [hfact σ hσU, hσ0, mul_zero]
        rw [horders σ hσU hσρ]
        exact hdvd σ hσU hfσ0
      have hfin_h : ∀ σ ∈ U, analyticOrderAt h σ ≠ ⊤ := by
        intro σ hσU
        by_cases hσρ : σ = ρ
        · subst hσρ
          rw [analyticOrderAt_eq_zero.mpr (Or.inr hhρ0)]
          exact ENat.zero_ne_top
        · rw [horders σ hσU hσρ]
          exact hfin σ hσU
      obtain ⟨u, huan, hupow⟩ := ih h U hUo hUsc hUpc hhan hZh hZh_card hdvd_h hfin_h
      -- assemble the root: (· - ρ)^q * u
      refine ⟨fun s => (s - ρ) ^ q * u s, ?_, ?_⟩
      · exact fun σ hσ => (((analyticAt_id.sub analyticAt_const).pow q).mul (huan σ hσ))
      · intro s hsU
        have : ((s - ρ) ^ q * u s) ^ n = (s - ρ) ^ (n * q) * (u s ^ n) := by
          rw [mul_pow, ← pow_mul, mul_comm q n]
        rw [this, hupow s hsU, ← hmnq, ← hfact s hsU]

/-- **Root existence ⟺ order divisibility.**  On a convex open `Ω` with a marked point `z₀`
where `f` does not vanish, and whose zero set meets every bounded piece `Ω ∩ ball z₀ (R+1)`
in a finite set, an analytic `n`-th root of `f` on `Ω` exists iff every vanishing order of
`f` on `Ω` is divisible by `n`. -/
theorem exists_root_iff_orders_dvd {f : ℂ → ℂ} {Ω : Set ℂ} {z₀ : ℂ} {n : ℕ} (hn : 0 < n)
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hz₀ : z₀ ∈ Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : f z₀ ≠ 0)
    (hZloc : ∀ R : ℕ, {s ∈ Ω ∩ ball z₀ ((R : ℝ) + 1) | f s = 0}.Finite) :
    (∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ n = f s) ↔
      ∀ ρ ∈ Ω, f ρ = 0 → (n : ℕ∞) ∣ analyticOrderAt f ρ := by
  constructor
  · rintro ⟨g, hgan, hgpow⟩ ρ hρ _
    exact root_orders_dvd hΩo hgan hgpow hρ
  intro hdvd
  classical
  -- finite orders everywhere on Ω
  have hord : ∀ ρ ∈ Ω, analyticOrderAt f ρ ≠ ⊤ := by
    intro ρ hρ htop
    have hev0 : f =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc.isPreconnected hρ hev0
    exact hf0 (this hz₀)
  -- the convex exhaustion pieces
  set W : ℕ → Set ℂ := fun R => Ω ∩ ball z₀ ((R : ℝ) + 1) with hW
  have hWo : ∀ R, IsOpen (W R) := fun R => hΩo.inter isOpen_ball
  have hWc : ∀ R, Convex ℝ (W R) := fun R => hΩc.inter (convex_ball _ _)
  have hWz : ∀ R, z₀ ∈ W R := fun R =>
    ⟨hz₀, mem_ball_self (by positivity)⟩
  have hWsub : ∀ R, W R ⊆ Ω := fun R => inter_subset_left
  have hWmono : ∀ {R R' : ℕ}, R ≤ R' → W R ⊆ W R' := by
    intro R R' hle
    exact inter_subset_inter_right _ (ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hle 1))
  have hWmem : ∀ s ∈ Ω, s ∈ W ⌈dist s z₀⌉₊ := by
    intro s hs
    refine ⟨hs, mem_ball.mpr ?_⟩
    calc dist s z₀ ≤ (⌈dist s z₀⌉₊ : ℝ) := Nat.le_ceil _
      _ < (⌈dist s z₀⌉₊ : ℝ) + 1 := lt_add_one _
  -- an n-th root value at the marked point, fixed once
  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_pow_nat_eq (f z₀) hn
  -- normalised roots on each piece
  have hroots : ∀ R : ℕ, ∃ g, AnalyticOnNhd ℂ g (W R) ∧ (∀ s ∈ W R, g s ^ n = f s) ∧
      g z₀ = w₀ := by
    intro R
    obtain ⟨u, huan, hupow⟩ :=
      exists_root_of_finite hn (hZloc R).toFinset.card f (W R) (hWo R)
        (isSimplyConnected_of_convex (hWc R) ⟨z₀, hWz R⟩) (hWc R).isPreconnected
        (hf.mono (hWsub R)) (hZloc R) le_rfl
        (fun ρ hρ h0 => hdvd ρ (hWsub R hρ) h0)
        (fun ρ hρ => hord ρ (hWsub R hρ))
    have huz : u z₀ ^ n = f z₀ := hupow z₀ (hWz R)
    have hu0 : u z₀ ≠ 0 := fun h => hf0 (by rw [← huz, h, zero_pow hn.ne'])
    refine ⟨fun s => (w₀ / u z₀) * u s, fun σ hσ => analyticAt_const.mul (huan σ hσ), ?_, ?_⟩
    · intro s hs
      rw [mul_pow, div_pow, hw₀, huz, div_self (by rw [← huz]; exact pow_ne_zero _ hu0),
        one_mul]
      exact hupow s hs
    · exact div_mul_cancel₀ w₀ hu0
  choose gR hgan hgpow hgz using hroots
  -- compatibility of the normalised roots
  have hcompat : ∀ R R' (s : ℂ), s ∈ W R → s ∈ W R' → gR R s = gR R' s := by
    have key : ∀ {R R' : ℕ}, R ≤ R' → ∀ s ∈ W R, gR R s = gR R' s := by
      intro R R' hle
      have := pow_root_unique hn (hWo R) (hWc R).isPreconnected (hgan R)
        ((hgan R').mono (hWmono hle))
        (hgpow R) (fun s hs => hgpow R' s (hWmono hle hs)) (hWz R) hf0
        ((hgz R).trans (hgz R').symm)
      exact fun s hs => this hs
    intro R R' s hsR hsR'
    rcases le_total R R' with hle | hle
    · exact key hle s hsR
    · exact (key hle s hsR').symm
  -- the glued global root
  refine ⟨fun s => if hs : s ∈ Ω then gR ⌈dist s z₀⌉₊ s else 0, ?_, ?_⟩
  · intro σ hσ
    have hσW : σ ∈ W ⌈dist σ z₀⌉₊ := hWmem σ hσ
    refine (hgan _ σ hσW).congr ?_
    filter_upwards [(hWo _).mem_nhds hσW] with z hz
    have hzΩ : z ∈ Ω := hWsub _ hz
    rw [dif_pos hzΩ]
    exact hcompat _ _ z hz (hWmem z hzΩ)
  · intro s hs
    simp only [dif_pos hs]
    exact hgpow _ s (hWmem s hs)

end RHTower
