import GaloisForLFunctions.HyperbolicArakelovTheory.CarriersWithAClosedDegreeGeodesic
import GaloisForLFunctions.RHTower.PrimeLogSeparationAperture

/-!
# Carriers at a conical limit point

The end `∞` of the degree geodesic is a **conical limit point** of a group `Γ ⊂ SL₂(ℂ)` when the
degree ray returns infinitely often to a bounded neighbourhood of an orbit: for some `R` and
infinitely many degrees `M` there is `γ_M ∈ Γ` with `d(z_M, γ_M z_1) ≤ R`. For convex cocompact
groups every limit point is conical, and every point of `∂ℍ³` is either a point of discontinuity or a
limit point; so this file, with `TheDilationLimitOfATwistedCarrier`, covers B118′.2 for every
geometrically finite group with `δ(Γ) < ½` (classical: `δ < ½` excludes parabolic elements).

**Theorem** (`not_carrierSum_eq_torsion_of_conical`). If `Σ_{γ≠1} e^{−d(z_1, γz_1)/2} < ∞` and `∞` is a
conical limit point, no twisted carrier of `Γ` with weights `‖w‖ ≤ 1` carries the torsion kernel.

**Mechanism.** Fix `P`. At a return `M`, move the pair by `γ_M^{−1}`: `x = γ_M^{−1}z_M` lies within `R`
of `z_1`, and `y_p = γ_M^{−1}z_{pM}` at distance `log p` from `x`.
* An image `g y_p` within distance `1` of `x` forces `d(z_1, gz_1) ≤ 2R + 1 + log P`
  (`exp_neg_half_h3Dist_le`); there are at most `K ≤ S e^{R + ½}√P` such `g`, `S` the Poincaré sum
  (`card_near_le`).
* The points `y_p`, `p ≤ P` prime, are `1/P`-separated (`inv_le_log_div`), so each near `g` comes
  within `1/(4P)` of `x` for at most one prime. Since the primes up to `P` outnumber `S e^{R + ½}√P`
  for large `P` (`exists_nat_card_primes_gt`, Chebyshev), some prime `p ≤ P` is **good**: every image
  of `y_p` stays at distance `≥ 1/(4P)` from `x`.
* For a good prime the Green majorant at `(M, pM)` is at most a fixed summable bound, near images
  by `2πG_{1/2}(1/(4P))`, far ones by `2e^{−d/2}` and the Poincaré weights (`archProfile_le_two_exp`).
Bounded geometry thus holds at `(M, p_M M)` for infinitely many `M` with `p_M` among finitely many
primes, and `CarriersOfBoundedGeometry` concludes by pigeonhole.
-/

open Filter Topology Set Asymptotics
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-- Far images: `2πG_{1/2}(d) ≤ 2e^{−d/2}` for `d ≥ 1`. -/
theorem archProfile_le_two_exp {d : ℝ} (hd : 1 ≤ d) : archProfile d ≤ 2 * Real.exp (-d / 2) := by
  unfold archProfile
  have h2 : Real.exp (-2) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
    have := Real.add_one_le_exp (2 : ℝ)
    norm_num; linarith
  have h1 : Real.exp (-2 * d) ≤ 1 / 2 :=
    (Real.exp_le_exp.mpr (by linarith)).trans h2
  have hpos : 0 < 1 - Real.exp (-2 * d) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [Real.exp_pos (-d / 2)]

/-- The triangle inequality against the base point at arbitrary points. -/
theorem exp_neg_half_h3Dist_le (g : SL2C) (x y : H3) :
    Real.exp (-(h3Dist x (h3Act g y)) / 2) ≤
      Real.exp ((h3Dist basePoint x + h3Dist basePoint y) / 2) * poincareWeight g := by
  rw [poincareWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := h3Dist_triangle basePoint x (h3Act g basePoint)
  have h2 := h3Dist_triangle x (h3Act g y) (h3Act g basePoint)
  have h3 : h3Dist (h3Act g y) (h3Act g basePoint) = h3Dist basePoint y := by
    rw [h3Dist_h3Act, h3Dist_comm]
  linarith

/-- At most `S e^{L/2}` elements move the base point by at most `L`. -/
theorem card_near_le {ι : Type*} {γ : ι → SL2C} (hP : Summable fun i => poincareWeight (γ i))
    (L : ℝ) :
    ((finite_near hP L).toFinset.card : ℝ) ≤ (∑' i, poincareWeight (γ i)) * Real.exp (L / 2) := by
  set s := (finite_near hP L).toFinset
  have h1 : ∑ i ∈ s, poincareWeight (γ i) ≤ ∑' i, poincareWeight (γ i) :=
    hP.sum_le_tsum s (fun i _ => poincareWeight_nonneg _)
  have h2 : ∀ i ∈ s, Real.exp (-L / 2) ≤ poincareWeight (γ i) := by
    intro i hi
    simp only [s, Set.Finite.mem_toFinset, mem_setOf_eq] at hi
    exact Real.exp_le_exp.mpr (by linarith)
  have h3 : (s.card : ℝ) * Real.exp (-L / 2) ≤ ∑ i ∈ s, poincareWeight (γ i) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum h2
  have h4 : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add, show -L / 2 + L / 2 = 0 by ring, Real.exp_zero]
  calc (s.card : ℝ) = s.card * Real.exp (-L / 2) * Real.exp (L / 2) := by
        rw [mul_assoc, h4, mul_one]
    _ ≤ (∑' i, poincareWeight (γ i)) * Real.exp (L / 2) :=
        mul_le_mul_of_nonneg_right (h3.trans h1) (Real.exp_pos _).le

/-- **The primes up to `P` outnumber any multiple of `√P`** (Chebyshev). -/
theorem exists_nat_card_primes_gt (A : ℝ) :
    ∃ P : ℕ, 2 ≤ P ∧ A * Real.sqrt P < ((RHTower.windowPrimes 1 P).card : ℝ) := by
  set A' := max A 0 with hA'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := Real.log 2 / 4 / (A' + 1) with hc
  have hc0 : 0 < c := by positivity
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log 2 / 2 ≤ RHTower.chebyshevPrimeLower x / x :=
    RHTower.tendsto_chebyshevPrimeLower_div_id.eventually
      (le_mem_nhds (show Real.log 2 / 2 < Real.log 2 by linarith))
  have h2 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ c * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hc0
  have h3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have hev := (h1.and (h2.and h3))
  obtain ⟨P, hP⟩ := ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev).exists
  obtain ⟨hcheb, hlog, hP3⟩ := hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hsq : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP0
  have hrpow : (P : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt P := (Real.sqrt_eq_rpow _).symm
  rw [Real.norm_of_nonneg hlogP.le, Real.norm_of_nonneg (by positivity), hrpow] at hlog
  refine ⟨P, by exact_mod_cast (show (2 : ℝ) ≤ P by linarith), ?_⟩
  have hcard := RHTower.chebyshevPrimeLower_div_log_le_card (x := (P : ℝ)) (by linarith)
  have hcheb' : Real.log 2 / 2 * P ≤ RHTower.chebyshevPrimeLower P := by
    rwa [le_div_iff₀ hP0] at hcheb
  -- `A √P log P ≤ A' c P < (log 2/2) P`
  have hsqsq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
  have hkey : A' * Real.sqrt P * Real.log P < Real.log 2 / 2 * P := by
    have : A' * Real.sqrt P * Real.log P ≤ A' * Real.sqrt P * (c * Real.sqrt P) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have e : A' * Real.sqrt P * (c * Real.sqrt P) = A' / (A' + 1) * (Real.log 2 / 4) * P := by
      rw [show A' * Real.sqrt P * (c * Real.sqrt P) = A' * c * (Real.sqrt P * Real.sqrt P) by ring,
        hsqsq, hc]
      ring
    have hA'0 : 0 ≤ A' := le_max_right _ _
    have hfrac : A' / (A' + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have : A' / (A' + 1) * (Real.log 2 / 4) * P < Real.log 2 / 2 * P := by
      have := mul_lt_mul_of_pos_right hfrac (show 0 < Real.log 2 / 4 * P by positivity)
      nlinarith
    linarith
  have hAA' : A * Real.sqrt P ≤ A' * Real.sqrt P :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hsq.le
  have : A' * Real.sqrt P < RHTower.chebyshevPrimeLower P / Real.log P := by
    rw [lt_div_iff₀ hlogP]; linarith
  linarith

/-- Distinct primes `p < p' ≤ P` give degree points `1/P` apart. -/
theorem inv_le_log_div {p p' P : ℕ} (hp : 0 < p) (hpp' : p < p') (hp'P : p' ≤ P) :
    1 / (P : ℝ) ≤ Real.log ((p' : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp'0 : (0 : ℝ) < p' := by exact_mod_cast (hp.trans hpp')
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hp'0 hp0)
  rw [inv_div] at h1
  have h2 : 1 / (P : ℝ) ≤ 1 / p' := one_div_le_one_div_of_le hp'0 (by exact_mod_cast hp'P)
  have h3 : 1 / (p' : ℝ) ≤ 1 - p / p' := by
    rw [div_le_iff₀ hp'0, sub_mul, div_mul_cancel₀ _ hp'0.ne', one_mul]
    have : (p : ℝ) + 1 ≤ p' := by exact_mod_cast hpp'
    linarith
  linarith

/-- **No carrier with a conical degree end carries the torsion** (B118′.2 at conical limit
points). Let `Γ ⊂ SL₂(ℂ)` have convergent Poincaré series at `½`, and let the degree ray return
infinitely often within `R` of `Γz_1`. For every weight `‖w‖ ≤ 1` on `Γ∖{1}` and every `κ ≠ 0`,
`Σ_{γ≠1} w(γ)·2πG_{1/2}(d(z_m, γz_n)) = κ·Λ(n/m)(n/m)^{−1/2}` fails. -/
theorem not_carrierSum_eq_torsion_of_conical {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {R : ℝ}
    (hcon : ∀ N : ℕ, ∃ M : ℕ, ∃ hM : 0 < M, N ≤ M ∧
      ∃ γ ∈ Γ, h3Dist (natPoint M hM) (h3Act γ basePoint) ≤ R)
    {w : Nontriv Γ → ℂ} (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum (fun i : Nontriv Γ => i.1) w m n = κ * (weilPrimeKernel m n : ℂ) := by
  set S := ∑' i : Nontriv Γ, poincareWeight i.1 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun i => poincareWeight_nonneg _
  obtain ⟨P, hP2, hPcard⟩ := exists_nat_card_primes_gt (S * Real.exp (R + 1 / 2))
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  set W := RHTower.windowPrimes 1 P with hW
  have hmemW : ∀ p ∈ W, p.Prime ∧ 1 < p ∧ p ≤ P := by
    intro p hp
    rw [hW, RHTower.mem_windowPrimes (by norm_num) hP0.le] at hp
    exact ⟨hp.1, by exact_mod_cast hp.2.1, by exact_mod_cast hp.2.2⟩
  set L := 2 * R + 1 + Real.log P with hL
  set N₀ := (finite_near hP L).toFinset with hN₀
  have hK : (N₀.card : ℝ) < (W.card : ℝ) := by
    have h := card_near_le hP L
    have he : Real.exp (L / 2) = Real.exp (R + 1 / 2) * Real.sqrt P := by
      rw [hL, show (2 * R + 1 + Real.log P) / 2 = (R + 1 / 2) + Real.log P / 2 by ring,
        Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hP0]
      ring_nf
    rw [he, ← mul_assoc] at h
    linarith
  set η := 1 / (4 * (P : ℝ)) with hη
  have hη0 : 0 < η := by positivity
  set C := 2 * Real.exp ((2 * R + Real.log P) / 2) with hC
  set b : Nontriv Γ → ℝ := fun g =>
    (if g ∈ N₀ then archProfile η else 0) + C * poincareWeight g.1 with hb
  have hb0 : ∀ g, 0 ≤ b g := by
    intro g
    have h1 : 0 ≤ (if g ∈ N₀ then archProfile η else 0) := by
      split_ifs
      · exact (archProfile_pos hη0).le
      · exact le_rfl
    exact add_nonneg h1 (mul_nonneg (by positivity) (poincareWeight_nonneg _))
  have hbsum : Summable b :=
    (summable_of_ne_finset_zero (s := N₀) fun g hg => by simp [hg]).add (hP.mul_left C)
  set B := ∑' g, b g + 1 with hB
  have hB0 : 0 < B := by
    have h : 0 ≤ ∑' g, b g := tsum_nonneg hb0
    linarith
  have hη1 : η < 1 := by
    have h2P : (2 : ℝ) ≤ P := by exact_mod_cast hP2
    rw [hη, div_lt_one (by positivity)]
    linarith
  -- **the key step**: at every return some prime `p ≤ P` has bounded geometry
  have hkey : ∀ (M : ℕ) (hM : 0 < M) (γ : SL2C), γ ∈ Γ →
      h3Dist (natPoint M hM) (h3Act γ basePoint) ≤ R →
      ∃ p ∈ W, BoundedGeometryAt (fun i : Nontriv Γ => i.1) p B M := by
    intro M hM γ hγ hR
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    set x := h3Act γ⁻¹ (natPoint M hM) with hx
    have e1 : h3Act γ x = natPoint M hM := by rw [hx, ← h3Act_mul, mul_inv_cancel, h3Act_one]
    have hxR : h3Dist basePoint x ≤ R := by
      rw [← h3Dist_h3Act γ, e1, h3Dist_comm]; exact hR
    have hW0 : ∀ p ∈ W, 0 < p := fun p hp => (hmemW p hp).1.pos
    let y : (p : ℕ) → 0 < p → H3 := fun p hp =>
      h3Act γ⁻¹ (degPoint ((p : ℝ) * M) (mul_pos (by exact_mod_cast hp) hM0))
    -- distances of the moved pair
    have hdxy : ∀ p (hp : p ∈ W), h3Dist x (y p (hW0 p hp)) = Real.log p := by
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hW0 p hp
      simp only [hx, y]
      rw [h3Dist_h3Act, show natPoint M hM = degPoint (M : ℝ) hM0 from rfl, h3Dist_degPoint,
        Real.log_mul hp0.ne' hM0.ne', add_sub_cancel_right,
        abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (hmemW p hp).2.1.le))]
    have hyR : ∀ p (hp : p ∈ W), h3Dist basePoint (y p (hW0 p hp)) ≤ R + Real.log P := by
      intro p hp
      have h1 := h3Dist_triangle basePoint x (y p (hW0 p hp))
      have h2 : Real.log p ≤ Real.log P :=
        Real.log_le_log (by exact_mod_cast hW0 p hp) (by exact_mod_cast (hmemW p hp).2.2)
      rw [hdxy p hp] at h1
      linarith
    have hnear : ∀ p (hp : p ∈ W) (g : Nontriv Γ),
        h3Dist x (h3Act g.1 (y p (hW0 p hp))) < 1 → g ∈ N₀ := by
      intro p hp g hg
      simp only [hN₀, Set.Finite.mem_toFinset, mem_setOf_eq]
      have h1 := h3Dist_triangle basePoint x (h3Act g.1 basePoint)
      have h2 := h3Dist_triangle x (h3Act g.1 (y p (hW0 p hp))) (h3Act g.1 basePoint)
      have h3 : h3Dist (h3Act g.1 (y p (hW0 p hp))) (h3Act g.1 basePoint) =
          h3Dist basePoint (y p (hW0 p hp)) := by
        rw [h3Dist_h3Act, h3Dist_comm]
      have := hyR p hp
      rw [hL]; linarith
    have hsep : ∀ p (hp : p ∈ W) p' (hp' : p' ∈ W), p ≠ p' →
        1 / (P : ℝ) ≤ h3Dist (y p (hW0 p hp)) (y p' (hW0 p' hp')) := by
      intro p hp p' hp' hne
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hW0 p hp
      have hp'0 : (0 : ℝ) < p' := by exact_mod_cast hW0 p' hp'
      simp only [y]
      rw [h3Dist_h3Act, h3Dist_degPoint, Real.log_mul hp'0.ne' hM0.ne',
        Real.log_mul hp0.ne' hM0.ne', add_sub_add_right_eq_sub]
      rcases lt_or_gt_of_ne hne with h | h
      · rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hp0 (by exact_mod_cast h))),
          ← Real.log_div hp'0.ne' hp0.ne']
        exact inv_le_log_div (hW0 p hp) h (hmemW p' hp').2.2
      · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (Real.log_lt_log hp'0 (by exact_mod_cast h))),
          ← Real.log_div hp0.ne' hp'0.ne']
        exact inv_le_log_div (hW0 p' hp') h (hmemW p hp).2.2
    -- the bad primes inject into the near elements
    set Bad := W.filter fun p => ∃ hp : p ∈ W, ∃ g ∈ N₀,
      h3Dist x (h3Act g.1 (y p (hW0 p hp))) < η with hBad
    have hBadcard : Bad.card ≤ N₀.card := by
      rcases isEmpty_or_nonempty (Nontriv Γ) with hE | hNe
      · have : Bad = ∅ := Finset.filter_false_of_mem fun p _ ⟨_, g, _, _⟩ => hE.elim g
        rw [this, Finset.card_empty]; exact Nat.zero_le _
      · have hch : ∀ p ∈ Bad, ∃ g ∈ N₀,
            ∃ hp : p ∈ W, h3Dist x (h3Act g.1 (y p (hW0 p hp))) < η := by
          intro p hp
          obtain ⟨hpW, g, hg, hd⟩ := (Finset.mem_filter.mp hp).2
          exact ⟨g, hg, hpW, hd⟩
        choose! φ hφN hφd using hch
        refine Finset.card_le_card_of_injOn φ (fun p hp => hφN p hp) ?_
        intro p hp p' hp' hpp'
        by_contra hne
        obtain ⟨hpW, h1⟩ := hφd p hp
        obtain ⟨hp'W, h2⟩ := hφd p' hp'
        rw [hpp'] at h1
        have h3 := h3Dist_triangle (h3Act (φ p').1 (y p (hW0 p hpW))) x
          (h3Act (φ p').1 (y p' (hW0 p' hp'W)))
        rw [h3Dist_h3Act, h3Dist_comm (h3Act (φ p').1 (y p (hW0 p hpW))) x] at h3
        have h4 := hsep p hpW p' hp'W hne
        have : 2 * η < 1 / (P : ℝ) := by rw [hη]; field_simp; norm_num
        linarith
    obtain ⟨p, hpW, hpgood⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show Bad.card < W.card from lt_of_le_of_lt hBadcard (by exact_mod_cast hK))
    have hgood : ∀ g : Nontriv Γ, η ≤ h3Dist x (h3Act g.1 (y p (hW0 p hpW))) := by
      intro g
      by_contra hlt
      push Not at hlt
      by_cases hg : g ∈ N₀
      · exact hpgood (Finset.mem_filter.mpr ⟨hpW, hpW, g, hg, hlt⟩)
      · exact hg (hnear p hpW g (hlt.trans hη1))
    -- the Green majorant of the moved pair is dominated by `b`
    set F : Nontriv Γ → ℝ := fun g => archProfile (h3Dist x (h3Act g.1 (y p (hW0 p hpW)))) with hF
    have hFb : ∀ g, F g ≤ b g := by
      intro g
      have hd := hgood g
      by_cases hg : g ∈ N₀
      · have : F g ≤ archProfile η := strictAntiOn_archProfile.antitoneOn (mem_Ioi.2 hη0)
          (mem_Ioi.2 (hη0.trans_le hd)) hd
        simp only [hb, hg, if_true]
        nlinarith [mul_nonneg (show 0 ≤ C by positivity) (poincareWeight_nonneg g.1)]
      · have hd1 : 1 ≤ h3Dist x (h3Act g.1 (y p (hW0 p hpW))) := by
          by_contra h1; push Not at h1; exact hg (hnear p hpW g h1)
        have h1 := archProfile_le_two_exp hd1
        have h2 := exp_neg_half_h3Dist_le g.1 x (y p (hW0 p hpW))
        have h3 : Real.exp ((h3Dist basePoint x + h3Dist basePoint (y p (hW0 p hpW))) / 2) ≤
            Real.exp ((2 * R + Real.log P) / 2) :=
          Real.exp_le_exp.mpr (by have := hyR p hpW; linarith)
        simp only [hb, hg, if_false, zero_add, hC]
        have := hyR p hpW
        calc F g ≤ 2 * Real.exp (-(h3Dist x (h3Act g.1 (y p (hW0 p hpW)))) / 2) := h1
          _ ≤ 2 * (Real.exp ((h3Dist basePoint x + h3Dist basePoint (y p (hW0 p hpW))) / 2) *
                poincareWeight g.1) := by linarith
          _ ≤ 2 * (Real.exp ((2 * R + Real.log P) / 2) * poincareWeight g.1) := by
              gcongr; exact poincareWeight_nonneg _
          _ = 2 * Real.exp ((2 * R + Real.log P) / 2) * poincareWeight g.1 := by ring
    have hF0 : ∀ g, 0 ≤ F g := fun g => by
      rcases (h3Dist_nonneg x (h3Act g.1 (y p (hW0 p hpW)))).eq_or_lt with h | h
      · simp only [hF, ← h, archProfile_zero, le_refl]
      · exact (archProfile_pos h).le
    have hFsum : Summable F := Summable.of_nonneg_of_le hF0 hFb hbsum
    -- transport to the pair `(M, pM)` by conjugation with `γ`
    set e := conjEquiv Γ hγ with he
    have hpM : (0 : ℝ) < p * M := mul_pos (by exact_mod_cast hW0 p hpW) hM0
    have hcosh : ∀ i : Nontriv Γ,
        imageCosh i.1 (M : ℝ) (p * M) = h3Cosh x (h3Act (e i).1 (y p (hW0 p hpW))) := by
      intro i
      have hstep : h3Act γ⁻¹ (h3Act i.1 (degPoint ((p : ℝ) * M) hpM)) =
          h3Act (e i).1 (y p (hW0 p hpW)) := by
        simp only [he, conjEquiv, Equiv.coe_fn_mk, y]
        rw [← h3Act_mul, ← h3Act_mul]
        congr 1
        group
      rw [← h3Cosh_degPoint_h3Act i.1 hM0 hpM, ← h3Cosh_h3Act γ⁻¹, hstep]
      rfl
    have hterm : ∀ i : Nontriv Γ,
        greenOfCosh (imageCosh i.1 (M : ℝ) (p * M)) = F (e i) := by
      intro i
      rw [hcosh i]; rfl
    have hcomp : (fun i : Nontriv Γ => greenOfCosh (imageCosh i.1 (M : ℝ) (p * M))) = F ∘ e := by
      funext i; exact hterm i
    refine ⟨p, hpW, fun i => ?_, ?_, ?_⟩
    · rw [hcosh i, ← cosh_h3Dist, Real.one_lt_cosh]
      exact (hη0.trans_le (hgood (e i))).ne'
    · rw [hcomp]; exact e.summable_iff.mpr hFsum
    · rw [hcomp]
      have h2 : ∑' i, (F ∘ e) i = ∑' i, F i := e.tsum_eq F
      rw [h2]
      have := Summable.tsum_le_tsum hFb hFsum hbsum
      linarith
  have hfreq : ∃ᶠ M : ℕ in atTop, ∃ p ∈ W, BoundedGeometryAt (fun i : Nontriv Γ => i.1) p B M := by
    rw [frequently_atTop]
    intro N
    obtain ⟨M, hM, hNM, γ, hγ, hR⟩ := hcon N
    exact ⟨M, hNM, hkey M hM γ hγ hR⟩
  exact not_carrierSum_eq_torsion_of_frequently_boundedGeometry hw hκ
    (fun p hp => (hmemW p hp).1) hB0 hfreq

end GaloisForLFunctions.HyperbolicArakelovTheory
