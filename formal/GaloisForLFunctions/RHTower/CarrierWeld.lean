/-
The carrier weld: an anchored event ledger from a split dominating member.

The chain grammar of the anchored ledger accepts the following canonical construction.
Take a member `F` that on the annulus charts SPLITS as a finite product of linear factors
centred in the hole times a cofactor `u` nonvanishing on the ball, and DOMINATES ξ there
(`‖ξ − F‖ < ‖F‖` pointwise).  Then a chain from `u` to ξ exists inside the grammar: each
linear factor enters by an exact monomial jump — the factorisation between consecutive
partial products is an identity, not an approximation — and one dominated move carries
the full product to ξ.  The event list is one `+1` per factor.

Two consequences.  First, a Rouché-type counting theorem with no argument principle: on
an isolating annulus the chain transports the cofactor's global root to roots of ξ whose
deck class is `exp(2πi·(#factors)/n)`, while the isolating deck-class identity reads the
same class as `exp(2πi·m/n)` with `m` the vanishing order of ξ at the centre; at a level
exceeding both counts the classes agree only if the counts do, so the factor count IS the
order.  Second, the weld: when the factor count is even the event list carries paired
flux with the constructed consecutive pairing, producing the anchored event ledger for ξ
on the annulus — and given such a member on an isolating annulus at every hypothetical
off-line zero, every off-line vanishing order is even.  The analytic burden of that rung
is thereby exactly the supply of the split, the domination, and the evenness of the
factor count.
-/
import GaloisForLFunctions.RHTower.IsolatingAnnulusRung
import GaloisForLFunctions.RHTower.EdgeEventLedger
import GaloisForLFunctions.RHTower.LedgerTelescope

namespace RHTower

open Complex Metric

/-! ### Simple zeros enter by exact monomial jumps -/

/-- **The jump extraction.**  From a cofactor `u`, the member multiplying in one linear
factor per listed hole centre is reached by a chain of `jump_in` moves whose
factorisations are exact identities between consecutive partial products: the grammar
accepts one simple zero per move and records the event `+1` each time. -/
theorem ledgerChainE_prod_jumps {a : ℂ} {r₀ R : ℝ} (zs : List ℂ) :
    ∀ u : ℂ → ℂ, (∀ ρ' ∈ zs, ‖ρ' - a‖ ≤ r₀) →
    LedgerChainE a r₀ R u (fun z => (zs.map (fun w => z - w)).prod * u z)
      (List.replicate zs.length 1) := by
  induction zs with
  | nil =>
      intro u _
      simpa using LedgerChainE.refl u
  | cons ρ' tl ih =>
      intro u hzs
      have hfun : (fun z => (List.map (fun w => z - w) (ρ' :: tl)).prod * u z) =
          (fun z => (List.map (fun w => z - w) tl).prod * ((z - ρ') * u z)) := by
        funext z
        simp only [List.map_cons, List.prod_cons]
        ring
      rw [hfun, List.length_cons, List.replicate_succ]
      have hrest := ih (fun z => (z - ρ') * u z)
        (fun ρ'' h => hzs ρ'' (List.mem_cons_of_mem _ h))
      have hjump : LedgerChainE a r₀ R u
          (fun z => (List.map (fun w => z - w) tl).prod * ((z - ρ') * u z))
          (((1 : ℕ) : ℤ) :: List.replicate tl.length 1) :=
        LedgerChainE.jump_in (m := 1) (hzs ρ' List.mem_cons_self)
          (fun z _ => by rw [pow_one]) hrest
      simpa using hjump

/-- **The chain from the cofactor to ξ.**  A member that splits on the charts into
hole-centred linear factors times the cofactor and dominates ξ there yields a ledger
chain from the cofactor to ξ recording one `+1` event per factor: the jumps supply the
factors and the dominated move closes the gap to ξ. -/
theorem ledgerChainE_to_xi_of_split_domination {ρ : ℂ} {r₀ R : ℝ} {zs : List ℂ}
    {u F : ℂ → ℂ}
    (hzs : ∀ ρ' ∈ zs, ‖ρ' - ρ‖ ≤ r₀)
    (hF : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
      F z = (zs.map (fun w => z - w)).prod * u z)
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖) :
    LedgerChainE ρ r₀ R u xi (List.replicate zs.length 1) := by
  have hchain1 := ledgerChainE_prod_jumps (R := R) zs u hzs
  have hstep : LedgerChainE ρ r₀ R
      (fun z => (zs.map (fun w => z - w)).prod * u z) xi [] := by
    refine LedgerChainE.dominated
      (fun z _ => xi_analyticOnNhd_univ z (Set.mem_univ z)) ?_ (LedgerChainE.refl xi)
    intro z hz
    have hFz := hF z hz
    simp only [← hFz]
    exact hdom z hz
  have := ledgerChainE_trans hchain1 hstep
  simpa using this

/-! ### Rouché-type counting on an isolating annulus, without the argument principle -/

/-- **The split member carries exactly the enclosed order.**  If a member splits on the
charts into `zs.length` hole-centred linear factors times a ball-nonvanishing cofactor
and dominates ξ there, then on an isolating annulus the vanishing order of ξ at the
centre equals the factor count: the chain transports the cofactor's global root to roots
of ξ of deck class `exp(2πi·zs.length/N)`, the isolating identity reads the class as
`exp(2πi·m/N)`, and at level `N = m + zs.length + 1` the two agree only when equal. -/
theorem enclosed_count_eq_of_split_domination {ρ : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    {zs : List ℂ} {u F : ℂ → ℂ}
    (hu_an : AnalyticOnNhd ℂ u (ball ρ R)) (hu_ne : ∀ z ∈ ball ρ R, u z ≠ 0)
    (hzs : ∀ ρ' ∈ zs, ‖ρ' - ρ‖ ≤ r₀)
    (hF : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
      F z = (zs.map (fun w => z - w)).prod * u z)
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖) :
    (analyticOrderAt xi ρ).toNat = zs.length := by
  set m := (analyticOrderAt xi ρ).toNat
  set n := zs.length
  set N := m + n + 1 with hN_def
  have hN : 0 < N := by omega
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  have hchainE := ledgerChainE_to_xi_of_split_domination hzs hF hdom
  have hsum : (List.replicate n (1 : ℤ)).sum = (n : ℤ) := by simp
  have hchain : LedgerChain ρ r₀ R u xi (n : ℤ) := by
    have := ledgerChainE_toChain hchainE
    rwa [hsum] at this
  obtain ⟨r, hran, hrpow⟩ := exists_global_root_of_nonvanishing hR hN hu_an hu_ne
  have hsubR : chartRA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  have hsubL : chartLA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHcls⟩ :=
    ledgerChain_transport h0 hrR hN hchain r r
      (fun z hz => hran z (hsubR hz)) (fun z hz => hran z (hsubL hz))
      (fun z hz => hrpow z (hsubR hz)) (fun z hz => hrpow z (hsubL hz))
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  have hrP : r (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hPmem.1)
    rw [h0', zero_pow hN.ne'] at this
    exact hu_ne _ (hsubR hPmem.1) this.symm
  have hrM : r (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hMmem.1)
    rw [h0', zero_pow hN.ne'] at this
    exact hu_ne _ (hsubR hMmem.1) this.symm
  rw [deckClass_self hrP hrM, mul_one] at hHcls
  have h2 := xi_deckClass_annulus_isolating ρ h0 hrR hiso hN hH₁ hH₂ hpH₁ hpH₂
  have h3 : exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / N) =
      exp (2 * (Real.pi : ℂ) * I * (n : ℂ) / N) := by
    rw [← h2, hHcls]
    norm_cast
  have hone : exp (2 * (Real.pi : ℂ) * I * ((((m : ℤ) - (n : ℤ)) : ℤ) : ℂ) / N) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * I * ((((m : ℤ) - (n : ℤ)) : ℤ) : ℂ) / N =
        2 * (Real.pi : ℂ) * I * (m : ℂ) / N - 2 * (Real.pi : ℂ) * I * (n : ℂ) / N by
      push_cast; ring]
    rw [Complex.exp_sub, h3, div_self (Complex.exp_ne_zero _)]
  have hdvd : ((N : ℕ) : ℤ) ∣ ((m : ℤ) - (n : ℤ)) :=
    (exp_two_pi_mul_int_div_eq_one_iff hN _).mp hone
  have hzero : ((m : ℤ) - (n : ℤ)) = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [abs_lt]
    constructor
    · omega
    · omega
  omega

/-! ### The weld -/

/-- **The anchored event ledger from an even split dominating member.**  With the split
and the domination in hand and the factor count even, the canonical chain's event list
is that many ones and carries paired flux with the constructed consecutive pairing: the
anchored event ledger for ξ on the annulus, with every clause supplied. -/
theorem anchoredEventLedger_of_carrier_domination {ρ : ℂ} {r₀ R : ℝ} {zs : List ℂ}
    {u F : ℂ → ℂ}
    (hu_an : AnalyticOnNhd ℂ u (ball ρ R)) (hu_ne : ∀ z ∈ ball ρ R, u z ≠ 0)
    (hzs : ∀ ρ' ∈ zs, ‖ρ' - ρ‖ ≤ r₀)
    (hF : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
      F z = (zs.map (fun w => z - w)).prod * u z)
    (hdom : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖)
    (heven : Even zs.length) :
    AnchoredEventLedger ρ r₀ R xi :=
  ⟨u, List.replicate zs.length 1, hu_an, hu_ne,
    ledgerChainE_to_xi_of_split_domination hzs hF hdom,
    ledgerFluxPaired_replicate_one (nonempty_bandEdgePairing_of_even heven.two_dvd)⟩

/-- **The base rung from carrier data.**  If every hypothetical off-line ξ-zero admits an
isolating annulus and a member that splits there into an even number of hole-centred
linear factors times a ball-nonvanishing cofactor and dominates ξ on the charts, then
every off-line vanishing order is even.  The analytic burden of the base rung is exactly
this supply — the domination, the split, and the evenness of the factor count. -/
theorem rhLadder_one_of_carrier_domination
    (hsupply : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∃ (r₀ R : ℝ) (zs : List ℂ) (u F : ℂ → ℂ),
      0 ≤ r₀ ∧ r₀ < R ∧ (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      (∀ ρ' ∈ zs, ‖ρ' - ρ‖ ≤ r₀) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        F z = (zs.map (fun w => z - w)).prod * u z) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖) ∧
      Even zs.length) :
    RHLadder 1 := by
  refine rhLadder_one_of_isolating_anchoredEventLedgers ?_
  intro ρ hρ h0
  obtain ⟨r₀, R, zs, u, F, h1, h2, hiso, hu_an, hu_ne, hzs, hF, hdom, heven⟩ :=
    hsupply ρ hρ h0
  exact ⟨r₀, R, h1, h2, hiso,
    anchoredEventLedger_of_carrier_domination hu_an hu_ne hzs hF hdom heven⟩

/-- **The supply is never vacuous and the interface is exactly the parity.**  On any
isolating annulus the peel itself is a split dominating member: ξ equals the product of
`m` central linear factors times its nonvanishing cofactor and dominates itself on the
charts, where it has no zero.  Every clause of the weld except the evenness of the count
is therefore always satisfiable — and since any split dominating member has count equal
to the vanishing order, the weld re-expresses the rung with no loss: its entire content
is the parity of the count of an INDEPENDENTLY supplied split member. -/
theorem exists_split_domination_of_isolating {ρ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) :
    ∃ (zs : List ℂ) (u F : ℂ → ℂ),
      AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
      (∀ ρ' ∈ zs, ‖ρ' - ρ‖ ≤ r₀) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        F z = (zs.map (fun w => z - w)).prod * u z) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, ‖xi z - F z‖ < ‖F z‖) ∧
      zs.length = (analyticOrderAt xi ρ).toNat := by
  obtain ⟨h, hhan, hh0, hfact⟩ := xi_peel_isolating_ball ρ hiso
  refine ⟨List.replicate (analyticOrderAt xi ρ).toNat ρ, h, xi, hhan, hh0, ?_, ?_, ?_,
    by simp⟩
  · intro ρ' hρ'
    rw [List.eq_of_mem_replicate hρ']
    simpa using h0
  · intro z hz
    have hzball : z ∈ ball ρ R := by
      rcases hz with hz | hz
      · exact hz.2.1
      · exact hz.2.1
    rw [List.map_replicate, List.prod_replicate]
    exact hfact z hzball
  · intro z hz
    have hzball : z ∈ ball ρ R := by
      rcases hz with hz | hz
      · exact hz.2.1
      · exact hz.2.1
    have hzne : z ≠ ρ := by
      rcases hz with hz | hz
      · exact fun he => hz.2.2 (by rw [he]; exact Metric.mem_closedBall_self h0)
      · exact fun he => hz.2.2 (by rw [he]; exact Metric.mem_closedBall_self h0)
    have hxne : xi z ≠ 0 := hiso z hzball hzne
    simpa using norm_pos_iff.mpr hxne

end RHTower
