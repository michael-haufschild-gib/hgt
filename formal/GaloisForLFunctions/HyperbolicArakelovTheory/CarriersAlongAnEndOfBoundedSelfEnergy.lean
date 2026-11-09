import GaloisForLFunctions.HyperbolicArakelovTheory.CarriersWithAClosedDegreeGeodesic
import GaloisForLFunctions.RHTower.PrimeLogSeparationAperture

/-!
# Carriers along an end of bounded self-energy

For `Γ ⊂ SL₂(ℂ)` let `D_Γ(t) = Σ_{γ≠1} e^{−d(z_t, γz_t)/2}` (`selfEnergy`). Since
`e^{−d/2} ≤ 2πG_{1/2}(d)`, `D_Γ(t)` is at most the self-energy `Σ_{γ≠1} 2πG_{1/2}(d(z_t, γz_t))` of
the point `z_t` in `Γ\ℍ³`, the automorphic Green function at `s = ½` with the free pole removed; the
two are comparable where no element moves `z_t` by less than `1` (`archProfile_le_two_exp`).

**Theorem** (`not_carrierSum_eq_torsion_of_selfEnergy`). If `Σ_{γ≠1} e^{−d(z_1, γz_1)/2} < ∞` and
`D_Γ(M) ≤ C` for infinitely many degrees `M`, no twisted carrier of `Γ` with weights `‖w‖ ≤ 1`
carries the torsion kernel. A twisted carrier needs the self-energy of the quotient to blow up
along the whole degree end.

**Corollary** (`not_carrierSum_eq_torsion_of_conical`). At a conical end, `d(z_M, γ_M z_1) ≤ R`
gives `D_Γ(M) ≤ e^R Σ_{γ≠1} e^{−d(z_1, γz_1)/2}` (`selfEnergy_le_of_near_orbit`).

**Mechanism.** Fix `P` and a degree `M` with `D_Γ(M) ≤ C`; put `x = z_M`, `y_p = z_{pM}`.
* An image `g y_p` within `1` of `x` forces `d(x, gx) ≤ 1 + log P`, and there are at most
  `C e^{½}√P` such `g` (`finite_card_le_of_summable_exp`).
* The points `y_p`, `p ≤ P` prime, are `1/P`-separated (`inv_le_log_div`), so each near `g` comes
  within `1/(4P)` of `x` for at most one prime. The primes up to `P` outnumber `C e^{½}√P` for large
  `P` (`exists_nat_card_primes_gt`, Chebyshev), so some prime `p ≤ P` is **good**: every image of
  `y_p` stays at distance `≥ 1/(4P)` from `x`.
* For a good prime the Green majorant at `(M, pM)` is at most `C e^{½}√P·2πG_{1/2}(1/(4P)) + 2√P C`:
  near images by `2πG_{1/2}(1/(4P))`, far ones by `2e^{−d(x, gy_p)/2} ≤ 2√P e^{−d(x, gx)/2}`.
Bounded geometry thus holds at `(M, p_M M)` for infinitely many `M` with `p_M ≤ P`, and
`CarriersOfBoundedGeometry` concludes by pigeonhole.
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

/-- A summable family `e^{−D_i/2}` has finitely many `D_i ≤ L`, at most `(Σ e^{−D_i/2})·e^{L/2}`. -/
theorem finite_card_le_of_summable_exp {ι : Type*} {D : ι → ℝ}
    (hs : Summable fun i => Real.exp (-(D i) / 2)) (L : ℝ) :
    ∃ hfin : {i | D i ≤ L}.Finite,
      (hfin.toFinset.card : ℝ) ≤ (∑' i, Real.exp (-(D i) / 2)) * Real.exp (L / 2) := by
  have hpos : 0 < Real.exp (-L / 2) := Real.exp_pos _
  have hfin : {i | D i ≤ L}.Finite := by
    have h2 := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
    refine (show {i | ¬ Real.exp (-(D i) / 2) < Real.exp (-L / 2)}.Finite by
      simpa [Filter.eventually_cofinite] using h2).subset fun i hi => ?_
    simp only [mem_setOf_eq, not_lt] at hi ⊢
    exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨hfin, ?_⟩
  set s := hfin.toFinset
  have h1 : ∑ i ∈ s, Real.exp (-(D i) / 2) ≤ ∑' i, Real.exp (-(D i) / 2) :=
    hs.sum_le_tsum s (fun i _ => (Real.exp_pos _).le)
  have h3 : (s.card : ℝ) * Real.exp (-L / 2) ≤ ∑ i ∈ s, Real.exp (-(D i) / 2) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [s, Set.Finite.mem_toFinset, mem_setOf_eq] at hi
    exact Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add, show -L / 2 + L / 2 = 0 by ring, Real.exp_zero]
  calc (s.card : ℝ) = s.card * Real.exp (-L / 2) * Real.exp (L / 2) := by
        rw [mul_assoc, h4, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (h3.trans h1) (Real.exp_pos _).le
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

/-! ## The self-energy along the degree ray -/

/-- The displacement weight `e^{−d(z_t, γz_t)/2}` of `γ` at the degree point `z_t`. -/
def rayWeight (g : SL2C) (t : ℝ) : ℝ := Real.exp (-(Real.arcosh (imageCosh g t t)) / 2)

/-- **Self-energy majorant** `D_Γ(t) = Σ_{γ≠1} e^{−d(z_t, γz_t)/2}` of the degree point `z_t`. -/
def selfEnergy (Γ : Subgroup SL2C) (t : ℝ) : ℝ := ∑' g : Nontriv Γ, rayWeight g.1 t

theorem rayWeight_eq (g : SL2C) {t : ℝ} (ht : 0 < t) :
    rayWeight g t = Real.exp (-(h3Dist (degPoint t ht) (h3Act g (degPoint t ht))) / 2) := by
  rw [rayWeight, h3Dist_degPoint_h3Act]

/-- Convergence at `½` at the base point gives convergence at every degree point. -/
theorem summable_rayWeight {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {t : ℝ} (ht : 0 < t) :
    Summable fun g : Nontriv Γ => rayWeight g.1 t :=
  Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
    (fun g => exp_neg_half_dist_le g.1 ht ht) (hP.mul_left _)

/-- **No carrier along an end of bounded self-energy carries the torsion.** Let `Γ ⊂ SL₂(ℂ)` have
convergent Poincaré series at `½` and `D_Γ(M) ≤ C` for infinitely many degrees `M`. For every
weight `‖w‖ ≤ 1` on `Γ∖{1}` and every `κ ≠ 0`,
`Σ_{γ≠1} w(γ)·2πG_{1/2}(d(z_m, γz_n)) = κ·Λ(n/m)(n/m)^{−1/2}` fails. -/
theorem not_carrierSum_eq_torsion_of_selfEnergy {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {C : ℝ}
    (hD : ∃ᶠ M : ℕ in atTop, selfEnergy Γ M ≤ C)
    {w : Nontriv Γ → ℂ} (hw : ∀ i, ‖w i‖ ≤ 1) {κ : ℂ} (hκ : κ ≠ 0) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      carrierSum (fun i : Nontriv Γ => i.1) w m n = κ * (weilPrimeKernel m n : ℂ) := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨P, hP2, hPcard⟩ := exists_nat_card_primes_gt (C' * Real.exp (1 / 2))
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  set W := RHTower.windowPrimes 1 P with hW
  have hmemW : ∀ p ∈ W, p.Prime ∧ 1 < p ∧ p ≤ P := by
    intro p hp
    rw [hW, RHTower.mem_windowPrimes (by norm_num) hP0.le] at hp
    exact ⟨hp.1, by exact_mod_cast hp.2.1, by exact_mod_cast hp.2.2⟩
  have hW0 : ∀ p ∈ W, 0 < p := fun p hp => (hmemW p hp).1.pos
  set sP := Real.exp (Real.log P / 2) with hsP
  have hsP0 : 0 < sP := Real.exp_pos _
  have hsPeq : sP = Real.sqrt P := by
    rw [hsP, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hP0]; ring_nf
  set L := 1 + Real.log P with hL
  set η := 1 / (4 * (P : ℝ)) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by
    have h2P : (2 : ℝ) ≤ P := by exact_mod_cast hP2
    rw [hη, div_lt_one (by positivity)]
    linarith
  set B := C' * Real.exp (1 / 2) * sP * archProfile η + 2 * sP * C' + 1 with hB
  have hB0 : 0 < B := by
    have := (archProfile_pos hη0).le
    have : 0 ≤ C' * Real.exp (1 / 2) * sP * archProfile η := by positivity
    have : 0 ≤ 2 * sP * C' := by positivity
    linarith
  -- **the key step**: at every degree of bounded self-energy some prime `p ≤ P` is good
  have hkey : ∀ M : ℕ, 0 < M → selfEnergy Γ M ≤ C →
      ∃ p ∈ W, BoundedGeometryAt (fun i : Nontriv Γ => i.1) p B M := by
    intro M hM hDM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    set x := degPoint (M : ℝ) hM0 with hx
    have hsx := summable_rayWeight hP hM0
    have hsx' : Summable fun g : Nontriv Γ => Real.exp (-(h3Dist x (h3Act g.1 x)) / 2) :=
      hsx.congr fun g => rayWeight_eq _ hM0
    have hDx : ∑' g : Nontriv Γ, Real.exp (-(h3Dist x (h3Act g.1 x)) / 2) ≤ C' := by
      have : selfEnergy Γ M = ∑' g : Nontriv Γ, Real.exp (-(h3Dist x (h3Act g.1 x)) / 2) :=
        tsum_congr fun g => rayWeight_eq _ hM0
      rw [← this]; exact hDM.trans (le_max_left _ _)
    obtain ⟨hfin, hcard⟩ := finite_card_le_of_summable_exp hsx' L
    set N₀ := hfin.toFinset with hN₀
    have hK : (N₀.card : ℝ) < (W.card : ℝ) := by
      have he : Real.exp (L / 2) = Real.exp (1 / 2) * sP := by
        rw [hL, hsP, ← Real.exp_add]; ring_nf
      have h1 : (N₀.card : ℝ) ≤ C' * Real.exp (1 / 2) * sP := by
        calc (N₀.card : ℝ) ≤ _ := hcard
          _ ≤ C' * Real.exp (L / 2) := mul_le_mul_of_nonneg_right hDx (Real.exp_pos _).le
          _ = C' * Real.exp (1 / 2) * sP := by rw [he]; ring
      rw [hsPeq] at h1
      linarith
    let y : (p : ℕ) → 0 < p → H3 := fun p hp =>
      degPoint ((p : ℝ) * M) (mul_pos (by exact_mod_cast hp) hM0)
    have hdxy : ∀ p (hp : p ∈ W), h3Dist (y p (hW0 p hp)) x = Real.log p := by
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hW0 p hp
      simp only [hx, y]
      rw [h3Dist_degPoint, Real.log_mul hp0.ne' hM0.ne', sub_add_cancel_right, abs_neg,
        abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (hmemW p hp).2.1.le))]
    have hlogP : ∀ p ∈ W, Real.log p ≤ Real.log P := fun p hp =>
      Real.log_le_log (by exact_mod_cast hW0 p hp) (by exact_mod_cast (hmemW p hp).2.2)
    -- `d(x, gx) ≤ d(x, g y_p) + log p`
    have htri : ∀ p (hp : p ∈ W) (g : Nontriv Γ),
        h3Dist x (h3Act g.1 x) ≤ h3Dist x (h3Act g.1 (y p (hW0 p hp))) + Real.log p := by
      intro p hp g
      have h1 := h3Dist_triangle x (h3Act g.1 (y p (hW0 p hp))) (h3Act g.1 x)
      rw [h3Dist_h3Act, hdxy p hp] at h1
      exact h1
    have hnear : ∀ p (hp : p ∈ W) (g : Nontriv Γ),
        h3Dist x (h3Act g.1 (y p (hW0 p hp))) < 1 → g ∈ N₀ := by
      intro p hp g hg
      simp only [hN₀, Set.Finite.mem_toFinset, mem_setOf_eq]
      have := htri p hp g
      have := hlogP p hp
      rw [hL]; linarith
    have hsep : ∀ p (hp : p ∈ W) p' (hp' : p' ∈ W), p ≠ p' →
        1 / (P : ℝ) ≤ h3Dist (y p (hW0 p hp)) (y p' (hW0 p' hp')) := by
      intro p hp p' hp' hne
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hW0 p hp
      have hp'0 : (0 : ℝ) < p' := by exact_mod_cast hW0 p' hp'
      simp only [y]
      rw [h3Dist_degPoint, Real.log_mul hp'0.ne' hM0.ne',
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
    -- the Green majorant at `(M, pM)` is dominated by `b`
    set F : Nontriv Γ → ℝ := fun g => archProfile (h3Dist x (h3Act g.1 (y p (hW0 p hpW))))
      with hF
    set b : Nontriv Γ → ℝ := fun g => (if g ∈ N₀ then archProfile η else 0) +
      2 * sP * Real.exp (-(h3Dist x (h3Act g.1 x)) / 2) with hb
    have hind : Summable fun g : Nontriv Γ => if g ∈ N₀ then archProfile η else 0 :=
      summable_of_ne_finset_zero (s := N₀) fun g hg => by simp [hg]
    have hbsum : Summable b := hind.add (hsx'.mul_left (2 * sP))
    have hFb : ∀ g, F g ≤ b g := by
      intro g
      have hd := hgood g
      have hexp0 := Real.exp_pos (-(h3Dist x (h3Act g.1 x)) / 2)
      by_cases hg : g ∈ N₀
      · have : F g ≤ archProfile η := strictAntiOn_archProfile.antitoneOn (mem_Ioi.2 hη0)
          (mem_Ioi.2 (hη0.trans_le hd)) hd
        simp only [hb, hg, if_true]
        nlinarith [mul_pos (show 0 < 2 * sP by positivity) hexp0]
      · have hd1 : 1 ≤ h3Dist x (h3Act g.1 (y p (hW0 p hpW))) := by
          by_contra h1; push Not at h1; exact hg (hnear p hpW g h1)
        have h1 := archProfile_le_two_exp hd1
        have h2 : Real.exp (-(h3Dist x (h3Act g.1 (y p (hW0 p hpW)))) / 2) ≤
            sP * Real.exp (-(h3Dist x (h3Act g.1 x)) / 2) := by
          rw [hsP, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have := htri p hpW g
          have := hlogP p hpW
          linarith
        simp only [hb, hg, if_false, zero_add]
        calc F g ≤ 2 * Real.exp (-(h3Dist x (h3Act g.1 (y p (hW0 p hpW)))) / 2) := h1
          _ ≤ 2 * (sP * Real.exp (-(h3Dist x (h3Act g.1 x)) / 2)) := by linarith
          _ = 2 * sP * Real.exp (-(h3Dist x (h3Act g.1 x)) / 2) := by ring
    have hF0 : ∀ g, 0 ≤ F g := fun g => by
      rcases (h3Dist_nonneg x (h3Act g.1 (y p (hW0 p hpW)))).eq_or_lt with h | h
      · simp only [hF, ← h, archProfile_zero, le_refl]
      · exact (archProfile_pos h).le
    have hFsum : Summable F := Summable.of_nonneg_of_le hF0 hFb hbsum
    have hbtsum : ∑' g, b g ≤ B - 1 := by
      have e1 : ∑' g : Nontriv Γ, (if g ∈ N₀ then archProfile η else 0) =
          N₀.card * archProfile η := by
        rw [tsum_eq_sum (s := N₀) fun g hg => if_neg hg,
          Finset.sum_congr rfl fun g hg => if_pos hg, Finset.sum_const, nsmul_eq_mul]
      have hNc : (N₀.card : ℝ) ≤ C' * Real.exp (1 / 2) * sP := by
        have he : Real.exp (L / 2) = Real.exp (1 / 2) * sP := by
          rw [hL, hsP, ← Real.exp_add]; ring_nf
        calc (N₀.card : ℝ) ≤ _ := hcard
          _ ≤ C' * Real.exp (L / 2) := mul_le_mul_of_nonneg_right hDx (Real.exp_pos _).le
          _ = C' * Real.exp (1 / 2) * sP := by rw [he]; ring
      rw [hb, hind.tsum_add (hsx'.mul_left (2 * sP)), e1, tsum_mul_left]
      have ha := (archProfile_pos hη0).le
      have h1 : (N₀.card : ℝ) * archProfile η ≤ C' * Real.exp (1 / 2) * sP * archProfile η :=
        mul_le_mul_of_nonneg_right hNc ha
      have h2 : 2 * sP * ∑' g : Nontriv Γ, Real.exp (-(h3Dist x (h3Act g.1 x)) / 2) ≤
          2 * sP * C' := mul_le_mul_of_nonneg_left hDx (by positivity)
      rw [hB]; linarith
    have hpM : (0 : ℝ) < p * M := mul_pos (by exact_mod_cast hW0 p hpW) hM0
    have hcomp : (fun i : Nontriv Γ => greenOfCosh (imageCosh i.1 (M : ℝ) (p * M))) = F := by
      funext i
      simp only [hF, y, hx, greenOfCosh]
      rw [h3Dist_degPoint_h3Act i.1 hM0 hpM]
    refine ⟨p, hpW, fun i => ?_, ?_, ?_⟩
    · rw [← h3Cosh_degPoint_h3Act i.1 hM0 hpM, ← cosh_h3Dist, Real.one_lt_cosh]
      exact (hη0.trans_le (hgood i)).ne'
    · rw [hcomp]; exact hFsum
    · rw [hcomp]
      have := Summable.tsum_le_tsum hFb hFsum hbsum
      linarith
  have hfreq : ∃ᶠ M : ℕ in atTop, ∃ p ∈ W, BoundedGeometryAt (fun i : Nontriv Γ => i.1) p B M :=
    (hD.and_eventually (eventually_gt_atTop 0)).mono fun M ⟨hDM, hM⟩ => hkey M hM hDM
  exact not_carrierSum_eq_torsion_of_frequently_boundedGeometry hw hκ
    (fun p hp => (hmemW p hp).1) hB0 hfreq

/-! ## Conical ends -/

/-- **A degree point near an orbit point has self-energy `≤ e^R·(Poincaré sum)`.** If
`d(z_t, γz_1) ≤ R` with `γ ∈ Γ`, then `d(γz_1, gγz_1) ≤ d(z_t, gz_t) + 2R`, and conjugation by `γ`
permutes `Γ∖{1}`. -/
theorem selfEnergy_le_of_near_orbit {Γ : Subgroup SL2C}
    (hP : Summable fun i : Nontriv Γ => poincareWeight i.1) {t R : ℝ} (ht : 0 < t) {γ : SL2C}
    (hγ : γ ∈ Γ) (hR : h3Dist (degPoint t ht) (h3Act γ basePoint) ≤ R) :
    selfEnergy Γ t ≤ Real.exp R * ∑' i : Nontriv Γ, poincareWeight i.1 := by
  set x := degPoint t ht with hx
  set e := conjEquiv Γ hγ with he
  have hle : ∀ g : Nontriv Γ, rayWeight g.1 t ≤ Real.exp R * poincareWeight (e g).1 := by
    intro g
    rw [rayWeight_eq _ ht, ← hx, poincareWeight, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- `d(z_1, γ⁻¹gγ z_1) = d(γz_1, gγz_1)`
    have hconj : h3Dist basePoint (h3Act (e g).1 basePoint) =
        h3Dist (h3Act γ basePoint) (h3Act g.1 (h3Act γ basePoint)) := by
      rw [← h3Dist_h3Act γ basePoint]
      congr 1
      simp only [he, conjEquiv, Equiv.coe_fn_mk]
      rw [← h3Act_mul, ← h3Act_mul]
      congr 1
      group
    have h1 := h3Dist_triangle (h3Act γ basePoint) x (h3Act g.1 (h3Act γ basePoint))
    have h2 := h3Dist_triangle x (h3Act g.1 x) (h3Act g.1 (h3Act γ basePoint))
    rw [h3Dist_h3Act] at h2
    have h1' : h3Dist (h3Act γ basePoint) x = h3Dist x (h3Act γ basePoint) := h3Dist_comm _ _
    have h3 : h3Dist x (h3Act γ basePoint) ≤ R := hR
    linarith
  have hsum : Summable fun g : Nontriv Γ => Real.exp R * poincareWeight (e g).1 :=
    (e.summable_iff.mpr hP).mul_left _
  calc selfEnergy Γ t ≤ ∑' g : Nontriv Γ, Real.exp R * poincareWeight (e g).1 :=
        Summable.tsum_le_tsum hle (summable_rayWeight hP ht) hsum
    _ = Real.exp R * ∑' i : Nontriv Γ, poincareWeight i.1 := by
        rw [tsum_mul_left]
        congr 1
        exact e.tsum_eq fun i : Nontriv Γ => poincareWeight i.1

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
  refine not_carrierSum_eq_torsion_of_selfEnergy hP (C := Real.exp R * ∑' i : Nontriv Γ,
    poincareWeight i.1) (frequently_atTop.mpr fun N => ?_) hw hκ
  obtain ⟨M, hM, hNM, γ, hγ, hR⟩ := hcon N
  exact ⟨M, hNM, selfEnergy_le_of_near_orbit hP (by exact_mod_cast hM) hγ hR⟩

end GaloisForLFunctions.HyperbolicArakelovTheory
