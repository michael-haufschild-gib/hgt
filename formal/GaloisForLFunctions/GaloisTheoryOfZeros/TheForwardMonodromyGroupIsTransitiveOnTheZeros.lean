import GaloisForLFunctions.GaloisTheoryOfZeros.AtARealSaddleEachStripOfTheWindowHoldsOneZero
import GaloisForLFunctions.GaloisTheoryOfZeros.TransportAlongRealTimesKeepsTheOrderOfTheZeros
import GaloisForLFunctions.GaloisTheoryOfZeros.EveryForwardMonodromyMovesFinitelyManyZeros

/-!
# The forward monodromy group is transitive on the zeros

**Theorem** (`exists_mem_forwardMonodromy_apply_eq`). For every forward time `b` off the branch
times and all zeros `p, q` of `H_b` some element of the forward monodromy group `G₊(b)` moves `p`
to `q`: the zero cover of the heat family over the forward half-plane is irreducible.

Proof. Base time `1/8`, where all zeros are real and simple. Given zeros `x, x'`, let `N` count
the zeros of `H_{1/8}` in the disc of radius `max(|x|, |x'|)`, let `R = π(N + 2) + 2`, and take a
real saddle `σ` far out, with signed loops of both signs beyond it.
* At `τ(σ)` each strip `πk < Re(σz) < π(k + 1)`, `−N − 1 ≤ k ≤ N`, holds exactly one zero, and
  every zero of the window lies in a strip.
* The zeros of adjacent strips `k, k − 1` are joined through simple zeros: along the real saddles
  and up a vertical segment to the base of the signed loop with `cos(πk) = −ε`, around the loop
  (the exchange), and back.
* Along the real times from `1/8` to `τ(σ)` the zeros keep their sign and their order. If `x`
  went beyond the strip `N`, the zeros of the strips `0, …, N` would come from `N + 1` distinct
  zeros of `H_{1/8}` between `0` and `x`. So `x` and `x'` go to strips of the window.
Other base times: a forward path from `b` to `1/8` carries the simple joins.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The strips of the window -/

theorem sin_pi_mul_int (k : ℤ) : Real.sin (π * k) = 0 := by
  rw [mul_comm]
  exact Real.sin_int_mul_pi k

/-- The strips `−N − 1 ≤ k ≤ N` lie in the window `R = π(N + 2) + 2`. -/
theorem abs_pi_mul_int_add_le {N : ℕ} {k : ℤ} (h1 : -(N : ℤ) - 1 ≤ k) (h2 : k ≤ N) :
    |π * k| + π + 2 ≤ π * (N + 2) + 2 := by
  have h1' : -(N : ℝ) - 1 ≤ k := by exact_mod_cast h1
  have h2' : (k : ℝ) ≤ N := by exact_mod_cast h2
  have hπ := Real.pi_pos
  rw [abs_mul, abs_of_pos hπ]
  have hk : |(k : ℝ)| ≤ N + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith [mul_le_mul_of_nonneg_left hk hπ.le]

/-- The facts at a real saddle `σ` for the window `R`: each strip holds a zero, and the zeros of
adjacent strips are joined through simple zeros. -/
structure RealSaddleWindow (R σ : ℝ) : Prop where
  one_le : 1 ≤ σ
  wide : WideRegion (σ : ℂ)
  facts : StripFacts R (σ : ℂ)
  exists_zero : ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R →
    ∃ z : ℂ, complexHeat (saddleTime (σ : ℂ)) z = 0 ∧ (σ : ℂ) * z ∈ cosStrip θ
  adjacent : ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R → |θ - π| + π + 2 ≤ R →
    ∀ z z' : ℂ, complexHeat (saddleTime (σ : ℂ)) z = 0 → (σ : ℂ) * z ∈ cosStrip θ →
    complexHeat (saddleTime (σ : ℂ)) z' = 0 → (σ : ℂ) * z' ∈ cosStrip (θ - π) →
    SimplyJoined (saddleTime (σ : ℂ)) z (saddleTime (σ : ℂ)) z'

/-- **Adjacent strips are joined.** For every window there is a real saddle at which each strip
holds a zero and the zeros of adjacent strips `θ`, `θ − π` are joined through simple zeros: from
the real saddle to the base of the signed loop of sign `ε = −cos θ` on the cosine side, around the
loop, which exchanges the two strips, and back. -/
theorem exists_realSaddleWindow (R : ℝ) : ∃ σ : ℝ, RealSaddleWindow R σ := by
  obtain ⟨σ₁, h50, hdom⟩ := exists_real_dominance
  obtain ⟨σ₂, hfacts⟩ := exists_stripFacts R
  obtain ⟨σ₃, hzero⟩ := exists_zero_mem_cosStrip R
  obtain ⟨σ₄, hpath⟩ := exists_simplyJoined_to_cosineSide R
  obtain ⟨σ₅, hex⟩ := exists_exchange R
  obtain ⟨σ, hσ₁, hσ₂, hσ₃, hσ₄, hσ₅⟩ : ∃ σ : ℝ, σ₁ ≤ σ ∧ σ₂ ≤ σ ∧ σ₃ ≤ σ ∧ σ₄ ≤ σ ∧ σ₅ ≤ σ :=
    ⟨max (max σ₁ σ₂) (max σ₃ (max σ₄ σ₅)), by simp⟩
  obtain ⟨ap, am, hp, hm, hpσ, hmσ⟩ := exists_isSignedLoop σ
  have hW := wideRegion_ofReal (h50.trans hσ₁)
  have hd := hdom σ hσ₁
  have hre : (σ : ℂ).re = σ := Complex.ofReal_re σ
  refine ⟨σ, by linarith, hW, hfacts _ hW (by rw [hre]; exact hσ₂) (cosineSide_of_dominance hd),
    fun θ hθ hθR => hzero _ hW (by rw [hre]; exact hσ₃) hd θ hθ hθR,
    fun θ hθ hθR hθR' z z' hz hzθ hz' hz'θ => ?_⟩
  have hθ' : Real.sin (θ - π) = 0 := by rw [Real.sin_sub_pi, hθ, neg_zero]
  -- the join around a signed loop of the right sign
  have join : ∀ {ε : ℂ} {a : ℝ → ℂ}, IsSignedLoop ε a → (ε = 1 ∨ ε = -1) →
      (∀ s, σ ≤ (a s).re) → (Real.cos θ : ℂ) = -ε →
      SimplyJoined (saddleTime (σ : ℂ)) z (saddleTime (σ : ℂ)) z' := by
    intro ε a h hε hfar hcos
    have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
    have hW0 : WideRegion (a 0) := (h.region 0).wide
    have hside := h.cosineSide hεn
    have hF0 : StripFacts R (a 0) := hfacts _ hW0 (hσ₂.trans (hfar 0)) hside
    obtain ⟨z₀, z₁, hz₀, hz₀θ, hz₁, hz₁θ, hj⟩ :=
      hex h hε (fun s => hσ₅.trans (hfar s)) θ hθ hcos hθR
    obtain ⟨v, hjv, hv, hvθ⟩ :=
      hpath σ hσ₄ (a 0) hW0 (hσ₄.trans (hfar 0)) hside θ hθ hθR z hz hzθ
    obtain ⟨v', hjv', hv', hv'θ⟩ :=
      hpath σ hσ₄ (a 0) hW0 (hσ₄.trans (hfar 0)) hside (θ - π) hθ' hθR' z' hz' hz'θ
    have e : v = z₀ :=
      hF0.injOn θ hθ hθR v z₀ (openCosStrip_subset θ hvθ) hz₀θ (by rw [hv, hz₀])
    have e' : v' = z₁ :=
      hF0.injOn (θ - π) hθ' hθR' v' z₁ (openCosStrip_subset _ hv'θ) hz₁θ (by rw [hv', hz₁])
    rw [e] at hjv
    rw [e'] at hjv'
    exact (hjv.trans hj).trans hjv'.symm
  rcases Real.sin_eq_zero_iff_cos_eq.mp hθ with hc | hc
  · exact join hm (Or.inr rfl) hmσ (by rw [hc]; norm_num)
  · exact join hp (Or.inl rfl) hpσ (by rw [hc]; norm_num)

/-- **All strips of the window are joined.** At a real saddle with joined adjacent strips, the
zeros of the strips `−N − 1 ≤ k, k' ≤ N` are joined through simple zeros. -/
theorem RealSaddleWindow.simplyJoined_strips {N : ℕ} {σ : ℝ}
    (hw : RealSaddleWindow (π * (N + 2) + 2) σ) {k k' : ℤ} (hk : -(N : ℤ) - 1 ≤ k)
    (hkN : k ≤ N) (hk' : -(N : ℤ) - 1 ≤ k') (hk'N : k' ≤ N) {z z' : ℂ}
    (hz : complexHeat (saddleTime (σ : ℂ)) z = 0) (hzk : (σ : ℂ) * z ∈ cosStrip (π * k))
    (hz' : complexHeat (saddleTime (σ : ℂ)) z' = 0) (hzk' : (σ : ℂ) * z' ∈ cosStrip (π * k')) :
    SimplyJoined (saddleTime (σ : ℂ)) z (saddleTime (σ : ℂ)) z' := by
  have hτ : 0 < (saddleTime (σ : ℂ)).re := hw.wide.time_re_pos
  obtain ⟨zb, hzb, hzbk⟩ := hw.exists_zero (π * ((-(N : ℤ) - 1 : ℤ) : ℝ)) (sin_pi_mul_int _)
    (abs_pi_mul_int_add_le le_rfl (by omega))
  have key : ∀ j : ℤ, -(N : ℤ) - 1 ≤ j → j ≤ N → ∀ u : ℂ,
      complexHeat (saddleTime (σ : ℂ)) u = 0 → (σ : ℂ) * u ∈ cosStrip (π * j) →
      SimplyJoined (saddleTime (σ : ℂ)) u (saddleTime (σ : ℂ)) zb := by
    intro j hj
    induction j, hj using Int.leInduction with
    | base =>
      intro _ u hu huk
      have hR := abs_pi_mul_int_add_le (N := N) (k := -(N : ℤ) - 1) le_rfl (by omega)
      have e : u = zb := hw.facts.injOn _ (sin_pi_mul_int _) hR u zb huk hzbk (by rw [hu, hzb])
      rw [e]
      exact SimplyJoined.refl hτ hzb (hw.facts.simple _ (sin_pi_mul_int _) hR zb hzbk)
    | succ j hj ih =>
      intro hjN u hu huk
      obtain ⟨v, hv, hvk⟩ :=
        hw.exists_zero (π * j) (sin_pi_mul_int j) (abs_pi_mul_int_add_le hj (by omega))
      have e : π * ((j + 1 : ℤ) : ℝ) - π = π * j := by
        push_cast
        ring
      have h1 := hw.adjacent (π * ((j + 1 : ℤ) : ℝ)) (sin_pi_mul_int _)
        (abs_pi_mul_int_add_le (by omega) hjN)
        (by rw [e]; exact abs_pi_mul_int_add_le hj (by omega)) u v hu huk hv
        (by rw [e]; exact hvk)
      exact h1.trans (ih (by omega) v hv hvk)
  exact (key k hk hkN z hz hzk).trans (key k' hk' hk'N z' hz' hzk').symm

/-! ## The zeros at `1/8` go into the window -/

/-- **A zero at `1/8` goes into the window.** Let `N` count the zeros of `H_{1/8}` in the disc of
radius `ρ`, and let a lift along the real times from `1/8` to `τ(σ)` start in that disc and end at
`y`. Then `σy < π(N + 1)`: otherwise the zeros of the strips `0, …, N`, all positive and below
`y`, come from `N + 1` distinct positive zeros of `H_{1/8}` below the start of the lift. -/
theorem RealSaddleWindow.lt_of_lift {N : ℕ} {σ ρ : ℝ} (hw : RealSaddleWindow (π * (N + 2) + 2) σ)
    (hN : (finite_zeros_closedBall ((1 / 8 : ℝ) : ℂ) ρ).toFinset.card = N) {w : ℝ → ℂ}
    (hwl : IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 w) (hx : ‖w 0‖ ≤ ρ) :
    σ * (w 1).re < π * (N + 1) := by
  by_contra hcon
  push Not at hcon
  have hT := eighth_le_realSaddleTime hw.one_le
  have h8 : (1 / 8 : ℝ) ≤ 1 / 8 := le_rfl
  have hσ0 : 0 < σ := by linarith [hw.one_le]
  have hπ := Real.pi_pos
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the zeros of the strips `0, …, N` and their lifts
  have hex : ∀ i ∈ Finset.range (N + 1), ∃ W : ℝ → ℂ,
      IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 W ∧
        (σ : ℂ) * W 1 ∈ cosStrip (π * ((i : ℤ) : ℝ)) := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨u, hu, huk⟩ := hw.exists_zero (π * ((i : ℤ) : ℝ)) (sin_pi_mul_int _)
      (abs_pi_mul_int_add_le (by omega) (by exact_mod_cast hiN))
    rw [saddleTime_ofReal] at hu
    obtain ⟨W, hW, hW1⟩ := exists_lift_ending_at h8 hT hu
    exact ⟨W, hW, by rw [hW1]; exact huk⟩
  choose! W hW hWk using hex
  have hstrip : ∀ i ∈ Finset.range (N + 1), (i : ℝ) ≤ N ∧
      π * i + 1 / 8 ≤ σ * (W i 1).re ∧ σ * (W i 1).re ≤ π * i + π - 1 / 8 := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨h1, h2, -, -⟩ := hWk i hi
    rw [Complex.re_ofReal_mul] at h1 h2
    push_cast at h1 h2
    exact ⟨by exact_mod_cast hiN, h1, h2⟩
  -- the strips lie below the end of the lift
  have hlt1 : ∀ i ∈ Finset.range (N + 1), (W i 1).re < (w 1).re := by
    intro i hi
    obtain ⟨hiN, -, h2⟩ := hstrip i hi
    have h3 : σ * (W i 1).re < σ * (w 1).re := by
      linarith [mul_le_mul_of_nonneg_left hiN hπ.le]
    exact lt_of_mul_lt_mul_left h3 hσ0.le
  -- the lifts keep the order of the strips
  have hord : ∀ j ∈ Finset.range (N + 1), ∀ j' ∈ Finset.range (N + 1), j < j' →
      (W j 0).re < (W j' 0).re := by
    intro j hj j' hj' hjj
    obtain ⟨-, -, h2⟩ := hstrip j hj
    obtain ⟨-, h1', -⟩ := hstrip j' hj'
    have hjj' : (j : ℝ) + 1 ≤ j' := by exact_mod_cast Nat.succ_le_of_lt hjj
    have h3 : σ * (W j 1).re < σ * (W j' 1).re := by
      linarith [mul_le_mul_of_nonneg_left hjj' hπ.le]
    exact (re_lt_iff_of_lifts h8 hT (hW j hj) (hW j' hj')).mpr
      (lt_of_mul_lt_mul_left h3 hσ0.le)
  -- the starts are zeros of `H_{1/8}` in the disc
  have hX : ∀ i ∈ Finset.range (N + 1),
      complexHeat ((1 / 8 : ℝ) : ℂ) (W i 0) = 0 ∧ ‖W i 0‖ ≤ ρ := by
    intro i hi
    have hz := (hW i hi).zero 0 h00
    rw [timeSeg_zero] at hz
    have him := (hW i hi).im_timeSeg h8 hT h00
    have hpos1 : 0 < (W i 1).re := by
      obtain ⟨-, h1, -⟩ := hstrip i hi
      have h2 := mul_nonneg hπ.le (Nat.cast_nonneg (α := ℝ) i)
      have h3 : 0 < σ * (W i 1).re := by linarith
      exact pos_of_mul_pos_right h3 hσ0.le
    have hpos0 : 0 < (W i 0).re := (re_pos_iff_of_lift h8 hT (hW i hi)).mpr hpos1
    have hlt : (W i 0).re < (w 0).re := (re_lt_iff_of_lifts h8 hT (hW i hi) hwl).mpr (hlt1 i hi)
    refine ⟨hz, ?_⟩
    rw [← Complex.abs_re_eq_norm.mpr him, abs_of_pos hpos0]
    linarith [Complex.re_le_norm (w 0)]
  have hinj : Set.InjOn (fun i => W i 0) (Finset.range (N + 1) : Set ℕ) := by
    intro i hi i' hi' heq
    have heq' : W i 0 = W i' 0 := heq
    rw [Finset.mem_coe] at hi hi'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hord i hi i' hi' h
      rw [heq'] at h1
      exact lt_irrefl _ h1
    · have h1 := hord i' hi' i hi h
      rw [heq'] at h1
      exact lt_irrefl _ h1
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range (N + 1))
    (t := (finite_zeros_closedBall ((1 / 8 : ℝ) : ℂ) ρ).toFinset) (fun i => W i 0) (fun i hi => by
    rw [Finset.mem_coe] at hi
    obtain ⟨hz, hn⟩ := hX i hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨mem_closedBall_zero_iff.mpr hn, hz⟩) hinj
  rw [Finset.card_range, hN] at hcard
  omega

/-! ## Transitivity -/

/-- **The zeros at `1/8` are joined through simple zeros.** -/
theorem simplyJoined_eighth {x x' : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0)
    (hx' : complexHeat ((1 / 8 : ℝ) : ℂ) x' = 0) :
    SimplyJoined ((1 / 8 : ℝ) : ℂ) x ((1 / 8 : ℝ) : ℂ) x' := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      (finite_zeros_closedBall ((1 / 8 : ℝ) : ℂ) (max ‖x‖ ‖x'‖)).toFinset.card = N := ⟨_, rfl⟩
  obtain ⟨σ, hw⟩ := exists_realSaddleWindow (π * (N + 2) + 2)
  have hT := eighth_le_realSaddleTime hw.one_le
  have h8 : (1 / 8 : ℝ) ≤ 1 / 8 := le_rfl
  have hσ0 : 0 < σ := by linarith [hw.one_le]
  have hπ := Real.pi_pos
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- a zero at `1/8` in the disc goes to a strip of the window
  have hgo : ∀ y : ℂ, complexHeat ((1 / 8 : ℝ) : ℂ) y = 0 → ‖y‖ ≤ max ‖x‖ ‖x'‖ →
      ∃ k : ℤ, -(N : ℤ) - 1 ≤ k ∧ k ≤ N ∧ ∃ u : ℂ, complexHeat (saddleTime (σ : ℂ)) u = 0 ∧
        (σ : ℂ) * u ∈ cosStrip (π * k) ∧
        SimplyJoined ((1 / 8 : ℝ) : ℂ) y (saddleTime (σ : ℂ)) u := by
    intro y hy hyρ
    obtain ⟨w, hwl, hw0⟩ := exists_lift_starting_at h8 hT hy
    have hj := hwl.simplyJoined_timeSeg h8 hT
    rw [hw0, ← saddleTime_ofReal] at hj
    have hu' := hwl.zero 1 h11
    rw [timeSeg_one] at hu'
    have hu : complexHeat (saddleTime (σ : ℂ)) (w 1) = 0 := by
      rw [saddleTime_ofReal]
      exact hu'
    have him := hwl.im_timeSeg h8 hT h11
    have hne : w 1 ≠ 0 := ne_zero_of_zero_ofReal hu'
    -- `σ|y₁| < π(N + 1)`, by the count applied to `y` or to `−y`
    have hbound : |σ * (w 1).re| < π * (N + 1) := by
      rcases lt_or_gt_of_ne (fun h : (w 1).re = 0 => hne (Complex.ext h him)) with hneg | hpos
      · have h1 : σ * (-w 1).re < π * (N + 1) :=
          hw.lt_of_lift hN hwl.neg (by show ‖-w 0‖ ≤ _; rw [norm_neg, hw0]; exact hyρ)
        rw [Complex.neg_re] at h1
        rw [abs_of_neg (mul_neg_of_pos_of_neg hσ0 hneg)]
        linarith
      · rw [abs_of_pos (mul_pos hσ0 hpos)]
        exact hw.lt_of_lift hN hwl (by rw [hw0]; exact hyρ)
    have hre : ((σ : ℂ) * w 1).re = σ * (w 1).re := Complex.re_ofReal_mul σ (w 1)
    have hnorm : ‖(σ : ℂ) * w 1‖ ≤ π * (N + 2) + 2 := by
      have him' : ((σ : ℂ) * w 1).im = 0 := by simp [him]
      rw [← Complex.abs_re_eq_norm.mpr him', hre]
      linarith
    have hmem := mem_openCosStrip_floor (hw.facts.collar (w 1) hu hnorm)
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊((σ : ℂ) * w 1).re / π⌋ := ⟨_, rfl⟩
    rw [← hk] at hmem
    have hmem' := hmem
    obtain ⟨m1, m2, -, -⟩ := hmem
    rw [hre] at m1 m2
    obtain ⟨b1, b2⟩ := abs_lt.mp hbound
    have hk1 : (-(N : ℝ) - 2) < k :=
      lt_of_mul_lt_mul_left (by linarith : π * (-(N : ℝ) - 2) < π * k) hπ.le
    have hk2 : (k : ℝ) < N + 1 :=
      lt_of_mul_lt_mul_left (by linarith : π * (k : ℝ) < π * (N + 1)) hπ.le
    have hk1' : -(N : ℤ) - 2 < k := by exact_mod_cast hk1
    have hk2' : k < (N : ℤ) + 1 := by exact_mod_cast hk2
    exact ⟨k, by omega, by omega, w 1, hu, openCosStrip_subset _ hmem', hj⟩
  obtain ⟨k, hk1, hk2, u, hu, huk, hj⟩ := hgo x hx (le_max_left _ _)
  obtain ⟨k', hk1', hk2', u', hu', huk', hj'⟩ := hgo x' hx' (le_max_right _ _)
  exact (hj.trans (hw.simplyJoined_strips hk1 hk2 hk1' hk2' hu huk hu' huk')).trans hj'.symm

/-- **The forward monodromy group is transitive on the zeros.** For every forward time `b` off the
branch times and all zeros `p, q` of `H_b` some `g ∈ G₊(b)` moves `p` to `q`. A forward path from
`b` to `1/8` carries the simple join of the transported zeros at `1/8` back to `b`. -/
theorem exists_mem_forwardMonodromy_apply_eq (b : ℂ) (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)
    (p q : {z : ℂ // complexHeat b z = 0}) : ∃ g ∈ forwardMonodromy b hb₀ hb, g p = q := by
  rw [← simplyJoined_iff_exists_mem_forwardMonodromy]
  have he : ((1 / 8 : ℝ) : ℂ) ∉ branchTimes := ofReal_not_mem_branchTimes_of_eighth_le le_rfl
  have he0 : 0 < ((1 / 8 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    norm_num
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isForwardPath hb₀ he0 hb he
  obtain ⟨p₁, hp⟩ := hγ.exists_transports (z₀ := p.1) (by rw [hγ0]; exact p.2)
  obtain ⟨q₁, hq⟩ := hγ.exists_transports (z₀ := q.1) (by rw [hγ0]; exact q.2)
  have hzero : ∀ {z z₁ : ℂ}, Transports γ z z₁ → complexHeat ((1 / 8 : ℝ) : ℂ) z₁ = 0 := by
    intro z z₁ hT
    obtain ⟨w, hw, -, rfl⟩ := hT
    have h := hw.zero 1 ⟨zero_le_one, le_rfl⟩
    rwa [hγ1] at h
  have Jp := hγ.simplyJoined hp
  have Jq := hγ.simplyJoined hq
  rw [hγ0, hγ1] at Jp Jq
  exact (Jp.trans (simplyJoined_eighth (hzero hp) (hzero hq))).trans Jq.symm

end

end GaloisForLFunctions.GaloisTheoryOfZeros
