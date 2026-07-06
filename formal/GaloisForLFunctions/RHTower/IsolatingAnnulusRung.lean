/-
The ladder rung from a single isolating annulus.

The rung from anchored ledgers consumes ledgers at arbitrarily small radii only to reach
one radius below the peel scale of ξ at the anchor.  But the peel cofactor of ξ is global,
so the deck-class identity holds on EVERY annulus whose ball meets no zero of ξ other than
its centre: nonvanishing of the cofactor away from the centre is the isolation hypothesis
itself.  The rung therefore follows from ONE isolating annulus per hypothetical off-line
zero — the consumer scale is the zero's isolation radius, not an arbitrarily small ε.
Isolating radii exist unconditionally (zeros of ξ are isolated), so the residual burden is
pairing the ledger with SOME isolating annulus: the producer and consumer scales meet
exactly when the isolation radius exceeds the producer's phase-π quantum.
-/
import GaloisForLFunctions.RHTower.LedgerReduction

namespace RHTower

open Complex Metric

/-- **Isolating radii exist.**  Around any point there is a ball on which ξ vanishes
nowhere except possibly at the centre: the peel writes ξ as a monomial times a cofactor
that is nonvanishing on a small ball, and the monomial vanishes only at the centre. -/
theorem xi_exists_isolating_radius (ρ : ℂ) :
    ∃ R > 0, ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0 := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ
  refine ⟨R₀, hR₀, fun z hz hzρ h0 => ?_⟩
  have hf := hfact z hz
  rw [h0] at hf
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzρ)) (hh0 z hz) hf.symm

/-- **The peel extends to any isolating ball.**  If ξ has no zero on `ball ρ₀ R` other
than possibly `ρ₀` itself, then `ξ = (z−ρ₀)^m · h` there with `h` analytic and
nonvanishing on the WHOLE ball: the global peel cofactor is nonzero at the centre by
peeling and nonzero away from it because ξ is. -/
theorem xi_peel_isolating_ball (ρ₀ : ℂ) {R : ℝ}
    (hiso : ∀ z ∈ ball ρ₀ R, z ≠ ρ₀ → xi z ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball ρ₀ R) ∧
      (∀ z ∈ ball ρ₀ R, h z ≠ 0) ∧
      ∀ z ∈ ball ρ₀ R, xi z = (z - ρ₀) ^ (analyticOrderAt xi ρ₀).toNat * h z := by
  have hm : analyticOrderAt xi ρ₀ = ((analyticOrderAt xi ρ₀).toNat : ℕ∞) :=
    (ENat.coe_toNat (xi_orderAt_ne_top ρ₀)).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ :=
    exists_peel isOpen_univ xi_analyticOnNhd_univ (Set.mem_univ ρ₀) hm
  refine ⟨h, fun z _ => hhan z (Set.mem_univ z), ?_, fun z _ => hfact z (Set.mem_univ z)⟩
  intro z hz
  by_cases hzρ : z = ρ₀
  · rwa [hzρ]
  · intro h0
    have hf := hfact z (Set.mem_univ z)
    rw [h0, mul_zero] at hf
    exact hiso z hz hzρ hf

/-- **The deck class of ξ counts the central multiplicity on any isolating annulus.**
For annulus data `0 ≤ r₀ < R` whose ball contains no zero of ξ besides the centre, any
local analytic `n`-th roots of ξ on the two slit annulus charts have deck class
`exp(2πi·m/n)`, `m` the vanishing order at the centre — no smallness of `R` needed. -/
theorem xi_deckClass_annulus_isolating (ρ₀ : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hiso : ∀ z ∈ ball ρ₀ R, z ≠ ρ₀ → xi z ≠ 0) {n : ℕ} (hn : 0 < n) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA ρ₀ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA ρ₀ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA ρ₀ r₀ R, G₁ z ^ n = xi z)
    (hpG₂ : ∀ z ∈ chartLA ρ₀ r₀ R, G₂ z ^ n = xi z) :
    deckClass G₁ G₂ (ρ₀ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (ρ₀ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * ((analyticOrderAt xi ρ₀).toNat : ℂ) / n) := by
  obtain ⟨h, hhan, hh0, hfact⟩ := xi_peel_isolating_ball ρ₀ hiso
  have hmz := deckClass_multi_zero (Finset.univ : Finset Unit) (fun _ => ρ₀)
    (fun _ => (analyticOrderAt xi ρ₀).toNat) h0 hrR hn
    (fun _ _ => by simpa using h0)
    hhan hh0
    (fun z hz => by
      have hprod : (∏ _i ∈ (Finset.univ : Finset Unit),
          (z - ρ₀) ^ (analyticOrderAt xi ρ₀).toNat) =
          (z - ρ₀) ^ (analyticOrderAt xi ρ₀).toNat := by simp
      rw [hprod]
      exact hfact z hz)
    hG₁ hG₂ hpG₁ hpG₂
  have hsum : (∑ _i ∈ (Finset.univ : Finset Unit),
      (((analyticOrderAt xi ρ₀).toNat : ℕ) : ℂ)) =
      ((analyticOrderAt xi ρ₀).toNat : ℂ) := by simp
  rw [hsum] at hmz
  exact hmz

/-- **The rung from a single isolating anchored ledger.**  If every hypothetical off-line
ξ-zero admits ONE annulus — of any size — whose ball is free of other ξ-zeros and which
carries an anchored ledger with net flux divisible by `2^k`, then every off-line vanishing
order is divisible by `2^k`.  The arbitrarily-small-radius clause of the rung is gone: the
consumer scale is the isolation radius. -/
theorem rhLadder_of_isolating_anchoredLedgers (k : ℕ)
    (hled : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∃ r₀ R : ℝ,
      0 ≤ r₀ ∧ r₀ < R ∧ (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      AnchoredLedger (2 ^ k) ρ r₀ R xi) :
    RHLadder k := by
  intro ρ hρ hzero
  obtain ⟨r₀, R, h0, hrR, hiso, f₀, flux, hf₀an, hf₀0, hchain, hdvd⟩ := hled ρ hρ hzero
  have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  obtain ⟨r, hran, hrpow⟩ := exists_global_root_of_nonvanishing hR h2k hf₀an hf₀0
  have hsubR : chartRA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  have hsubL : chartLA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHcls⟩ :=
    ledgerChain_transport h0 hrR h2k hchain r r
      (fun z hz => hran z (hsubR hz)) (fun z hz => hran z (hsubL hz))
      (fun z hz => hrpow z (hsubR hz)) (fun z hz => hrpow z (hsubL hz))
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  have hrP : r (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hPmem.1)
    rw [h0', zero_pow h2k.ne'] at this
    exact hf₀0 _ (hsubR hPmem.1) this.symm
  have hrM : r (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hMmem.1)
    rw [h0', zero_pow h2k.ne'] at this
    exact hf₀0 _ (hsubR hMmem.1) this.symm
  have h1 : deckClass H₁ H₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 := by
    rw [hHcls, deckClass_self hrP hrM, mul_one]
    exact exp_two_pi_mul_int_div_eq_one h2k hdvd
  have h2 := xi_deckClass_annulus_isolating ρ h0 hrR hiso h2k hH₁ hH₂ hpH₁ hpH₂
  rw [h1] at h2
  have hdvd2 : 2 ^ k ∣ (analyticOrderAt xi ρ).toNat :=
    (exp_two_pi_mul_div_eq_one_iff h2k _).mp h2.symm
  have hm : (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) = analyticOrderAt xi ρ :=
    ENat.coe_toNat (xi_orderAt_ne_top ρ)
  obtain ⟨c, hc⟩ := hdvd2
  rw [← hm, hc]
  exact ⟨(c : ℕ∞), by push_cast; ring⟩

/-- **The base rung from a single isolating event ledger.**  If every hypothetical
off-line ξ-zero admits ONE isolating annulus carrying an event-typed ledger chain whose
event list has paired flux, then every off-line vanishing order is even.  The consumer of
the paired-flux interface now demands events at one scale only — the isolation radius of
the zero — rather than at all scales. -/
theorem rhLadder_one_of_isolating_anchoredEventLedgers
    (hled : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∃ r₀ R : ℝ,
      0 ≤ r₀ ∧ r₀ < R ∧ (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      AnchoredEventLedger ρ r₀ R xi) :
    RHLadder 1 := by
  refine rhLadder_of_isolating_anchoredLedgers 1 ?_
  intro ρ hρ h0
  obtain ⟨r₀, R, h1, h2, hiso, hAE⟩ := hled ρ hρ h0
  refine ⟨r₀, R, h1, h2, hiso, ?_⟩
  rw [pow_one]
  exact anchoredLedger_two_of_eventLedger hAE

end RHTower
