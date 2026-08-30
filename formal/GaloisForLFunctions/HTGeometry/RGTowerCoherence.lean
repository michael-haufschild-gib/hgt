import GaloisForLFunctions.HTGeometry.LinearizedTowerCoherence
import GaloisForLFunctions.HTGeometry.MeromorphicMultiplicativeTranslationDefect
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnClosure
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnSum

/-!
# The coherence obstruction for a renormalization tower

An analytically linearizable germ at a hyperbolic fixed point has iterates
`f^n = Φ ∘ (λ^n · κ)`, where `Φ` is the linearizing coordinate and `κ` its local inverse.  The exact
beta field `β = (log λ) κ / κ'` is differentially algebraic exactly when `κ` is — the two differ by
a logarithmic derivative — and differential algebraicity of `κ` passes to `Φ` by local inversion.

Consequently a differentially algebraic beta field forces the whole tower into one autonomous
algebraic differential equation: **differential incoherence of the tower is an obstruction to
differential algebraicity of the exact generator.**
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Bottcher

noncomputable section

/-! ## Jets on an open set where two functions agree -/

/-- Functions agreeing on an open set have the same iterated derivatives there.  (This restates
`eqOn_iteratedDeriv_of_eqOn`, which is only reachable through the Bohr-carrier import chain, off
that stack.) -/
private theorem eqOn_iteratedDeriv_of_eqOn_open {U : Set ℂ} (hUo : IsOpen U) {f g : ℂ → ℂ}
    (h : Set.EqOn f g U) (k : ℕ) : Set.EqOn (iteratedDeriv k f) (iteratedDeriv k g) U := by
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero, iteratedDeriv_zero]
      exact h hz
  | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact Set.EqOn.deriv ih hUo hz

/-! ## Iterates of a linearizable germ -/

/-- **Equation (7).**  The iterates of a linearizable germ are the linearizing coordinate applied
to the scaled inverse coordinate. -/
theorem iterate_apply_linearizer {V : Set ℂ} {f Φ : ℂ → ℂ} {lam : ℂ}
    (hmaps : Set.MapsTo (fun z => lam * z) V V) (hlin : ∀ z ∈ V, f (Φ z) = Φ (lam * z)) :
    ∀ (n : ℕ), ∀ z ∈ V, f^[n] (Φ z) = Φ (lam ^ n * z) := by
  intro n
  induction n with
  | zero =>
      intro z _
      simp
  | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply, hlin z hz, ih (lam * z) (hmaps hz)]
      congr 1
      ring

/-- The iterates read on the source domain. -/
theorem iterate_eqOn_linearizer {U V : Set ℂ} {f Φ κ : ℂ → ℂ} {lam : ℂ}
    (hκV : Set.MapsTo κ U V) (hΦκ : ∀ t ∈ U, Φ (κ t) = t)
    (hmaps : Set.MapsTo (fun z => lam * z) V V) (hlin : ∀ z ∈ V, f (Φ z) = Φ (lam * z)) (n : ℕ) :
    Set.EqOn (f^[n]) (fun s => Φ (lam ^ n * κ s)) U := by
  intro t ht
  have h := iterate_apply_linearizer hmaps hlin n (κ t) (hκV ht)
  rw [hΦκ t ht] at h
  exact h

/-! ## The exact beta field -/

/-- The exact beta field of a linearizing coordinate, for a chosen logarithm of the multiplier. -/
def rgBeta (lamLog : ℂ) (κ : ℂ → ℂ) : ℂ → ℂ := fun t => lamLog * κ t / deriv κ t

theorem analyticOnNhd_rgBeta {U : Set ℂ} {κ : ℂ → ℂ} (hκ : AnalyticOnNhd ℂ κ U)
    (hκ'ne : ∀ t ∈ U, deriv κ t ≠ 0) (lamLog : ℂ) :
    AnalyticOnNhd ℂ (rgBeta lamLog κ) U :=
  (analyticOnNhd_const.mul hκ).div hκ.deriv hκ'ne

theorem rgBeta_ne_zero {U : Set ℂ} {κ : ℂ → ℂ} (hκne : ∀ t ∈ U, κ t ≠ 0)
    (hκ'ne : ∀ t ∈ U, deriv κ t ≠ 0) {lamLog : ℂ} (hlam : lamLog ≠ 0) :
    ∀ t ∈ U, rgBeta lamLog κ t ≠ 0 := by
  intro t ht
  show lamLog * κ t / deriv κ t ≠ 0
  exact div_ne_zero (mul_ne_zero hlam (hκne t ht)) (hκ'ne t ht)

theorem logDeriv_eqOn_rgBeta {U : Set ℂ} {κ : ℂ → ℂ} (hκne : ∀ t ∈ U, κ t ≠ 0)
    (hκ'ne : ∀ t ∈ U, deriv κ t ≠ 0) {lamLog : ℂ} (hlam : lamLog ≠ 0) :
    Set.EqOn (fun z => lamLog / rgBeta lamLog κ z) (fun z => deriv κ z / κ z) U := by
  intro t ht
  have h1 := hκne t ht
  have h2 := hκ'ne t ht
  show lamLog / (lamLog * κ t / deriv κ t) = deriv κ t / κ t
  field_simp

/-- **Equation (6), forward.**  A differentially algebraic beta field forces a differentially
algebraic linearizing coordinate. -/
theorem differentiallyAlgebraicOn_of_rgBeta {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {κ : ℂ → ℂ} (hκ : AnalyticOnNhd ℂ κ U)
    (hκne : ∀ t ∈ U, κ t ≠ 0) (hκ'ne : ∀ t ∈ U, deriv κ t ≠ 0) {lamLog : ℂ} (hlam : lamLog ≠ 0)
    (hβ : DifferentiallyAlgebraicOn (rgBeta lamLog κ) U) : DifferentiallyAlgebraicOn κ U := by
  have hβan := analyticOnNhd_rgBeta hκ hκ'ne lamLog
  have hβne := rgBeta_ne_zero hκne hκ'ne hlam
  have hquot : DifferentiallyAlgebraicOn (fun z => lamLog / rgBeta lamLog κ z) U :=
    differentiallyAlgebraicOn_div hUo hUc hUne hUinf analyticOnNhd_const hβan hβne
      (differentiallyAlgebraicOn_const U lamLog) hβ
  have hlog : DifferentiallyAlgebraicOn (fun z => deriv κ z / κ z) U :=
    differentiallyAlgebraicOn_of_eqOn hUo (logDeriv_eqOn_rgBeta hκne hκ'ne hlam) hquot
  exact (differentiallyAlgebraicOn_logDeriv_iff hUo hUc hUne hUinf hκ hκne).mp hlog

/-- **Equation (6), backward.**  A differentially algebraic linearizing coordinate has a
differentially algebraic beta field. -/
theorem differentiallyAlgebraicOn_rgBeta {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {κ : ℂ → ℂ} (hκ : AnalyticOnNhd ℂ κ U)
    (hκne : ∀ t ∈ U, κ t ≠ 0) (hκ'ne : ∀ t ∈ U, deriv κ t ≠ 0) (lamLog : ℂ)
    (hκDA : DifferentiallyAlgebraicOn κ U) : DifferentiallyAlgebraicOn (rgBeta lamLog κ) U := by
  have hlog : DifferentiallyAlgebraicOn (fun z => deriv κ z / κ z) U :=
    (differentiallyAlgebraicOn_logDeriv_iff hUo hUc hUne hUinf hκ hκne).mpr hκDA
  have hlogan : AnalyticOnNhd ℂ (fun z => deriv κ z / κ z) U := hκ.deriv.div hκ hκne
  have hderiv : DifferentiallyAlgebraicOn (deriv κ) U := by
    refine differentiallyAlgebraicOn_of_eqOn hUo ?_
      (differentiallyAlgebraicOn_mul hUo hUc hUne hUinf hlogan hκ hlog hκDA)
    intro t ht
    have h1 := hκne t ht
    field_simp
  exact differentiallyAlgebraicOn_div hUo hUc hUne hUinf
    (analyticOnNhd_const.mul hκ) hκ.deriv hκ'ne
    (differentiallyAlgebraicOn_const_mul hUo hUc hUne hUinf lamLog hκ hκDA) hderiv

/-! ## The coherence obstruction -/

/-- An autonomous relation among the jets is in particular an algebraic differential equation. -/
theorem differentiallyAlgebraicOn_of_autonomous_relation {U : Set ℂ} {h : ℂ → ℂ} {r : ℕ}
    {Q : MvPolynomial (Fin (r + 1)) ℂ} (hQ0 : Q ≠ 0)
    (hQ : ∀ t ∈ U, MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) h t) Q = 0) :
    DifferentiallyAlgebraicOn h U := by
  refine ⟨r, MvPolynomial.rename Fin.succ Q, ?_, fun z hz => ?_⟩
  · intro h0
    refine hQ0 (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective (r + 1)) ?_)
    rw [h0, map_zero]
  · rw [MvPolynomial.eval_rename]
    have hcomp : (Fin.cons z fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) h z) ∘ Fin.succ
        = fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) h z := by
      funext k
      simp
    rw [hcomp]
    exact hQ z hz

/-- **The coherence obstruction theorem, contrapositive form.**  A differentially algebraic
linearizing coordinate forces the whole tower of iterates into one autonomous algebraic
differential equation. -/
theorem exists_uniform_jet_relation_of_rgTower
    {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {f Φ κ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U)
    (hκV : Set.MapsTo κ U V) (hΦU : Set.MapsTo Φ V U)
    (hΦκ : ∀ t ∈ U, Φ (κ t) = t) (hκΦ : ∀ z ∈ V, κ (Φ z) = z)
    {lam : ℂ} (hlin : ∀ z ∈ V, f (Φ z) = Φ (lam * z))
    (hscale : Set.MapsTo (fun z => lam * z) V V)
    (hmaps : ∀ n : ℕ, Set.MapsTo (fun t => lam ^ n * κ t) U V)
    (hfaith : ∀ n : ℕ, SubstitutionFaithful U V (fun t => lam ^ n * κ t))
    (hκDA : DifferentiallyAlgebraicOn κ U) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ), Q ≠ 0 ∧
      ∀ (n : ℕ), ∀ t ∈ U, MvPolynomial.eval
        (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (f^[n]) t) Q = 0 := by
  have hΦDA : DifferentiallyAlgebraicOn Φ V :=
    differentiallyAlgebraicOn_of_localInverse hUo hUc hUne hUinf hΦ hκ hκV hΦU hΦκ hκΦ hκDA
  obtain ⟨r, Q, hQ0, hQ⟩ := exists_uniform_jet_relation_of_linearized_tower hUo hUc hUne hUinf
    hVo hVc hVne hVinf hΦ hκ hmaps hfaith hΦDA hκDA
  refine ⟨r, Q, hQ0, fun n t ht => ?_⟩
  have hiter := iterate_eqOn_linearizer hκV hΦκ hscale hlin n
  rw [show (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (f^[n]) t)
      = fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (fun s => Φ (lam ^ n * κ s)) t from
    funext fun k => eqOn_iteratedDeriv_of_eqOn_open hUo hiter (k : ℕ) ht]
  exact hQ n t ht

/-- **The coherence obstruction theorem `(5)`.**  Differential incoherence of the RG tower forces
the exact beta field to be hypertranscendental. -/
theorem not_differentiallyAlgebraicOn_rgBeta_of_incoherent
    {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {f Φ κ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U)
    (hκV : Set.MapsTo κ U V) (hΦU : Set.MapsTo Φ V U)
    (hΦκ : ∀ t ∈ U, Φ (κ t) = t) (hκΦ : ∀ z ∈ V, κ (Φ z) = z)
    (hκne : ∀ t ∈ U, κ t ≠ 0) (hκ'ne : ∀ t ∈ U, deriv κ t ≠ 0)
    {lam : ℂ} (hlin : ∀ z ∈ V, f (Φ z) = Φ (lam * z))
    (hscale : Set.MapsTo (fun z => lam * z) V V)
    (hmaps : ∀ n : ℕ, Set.MapsTo (fun t => lam ^ n * κ t) U V)
    (hfaith : ∀ n : ℕ, SubstitutionFaithful U V (fun t => lam ^ n * κ t))
    {lamLog : ℂ} (hlamLog : lamLog ≠ 0)
    (hincoh : ¬ ∃ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ), Q ≠ 0 ∧
      ∀ (n : ℕ), ∀ t ∈ U, MvPolynomial.eval
        (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (f^[n]) t) Q = 0) :
    ¬ DifferentiallyAlgebraicOn (rgBeta lamLog κ) U := by
  intro hβ
  exact hincoh (exists_uniform_jet_relation_of_rgTower hUo hUc hUne hUinf hVo hVc hVne hVinf
    hΦ hκ hκV hΦU hΦκ hκΦ hlin hscale hmaps hfaith
    (differentiallyAlgebraicOn_of_rgBeta hUo hUc hUne hUinf hκ hκne hκ'ne hlamLog hβ))

/-! ## Composition closure and scheme invariance -/

/-- **Composition closure.**  Across a faithful substitution the composite of two differentially
algebraic germs is again differentially algebraic — indeed autonomously so. -/
theorem differentiallyAlgebraicOn_comp
    {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {Φ g : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hg : AnalyticOnNhd ℂ g U)
    (hmaps : Set.MapsTo g U V) (hfaith : SubstitutionFaithful U V g)
    (hΦDA : DifferentiallyAlgebraicOn Φ V) (hgDA : DifferentiallyAlgebraicOn g U) :
    DifferentiallyAlgebraicOn (fun t => Φ (g t)) U := by
  have hmaps' : ∀ n : ℕ, Set.MapsTo (fun t => (1 : ℂ) ^ n * g t) U V := by
    intro n t ht
    simpa using hmaps ht
  have hfaith' : ∀ n : ℕ, SubstitutionFaithful U V (fun t => (1 : ℂ) ^ n * g t) := by
    intro n F hF hvan z hz
    refine hfaith F hF (fun t ht => ?_) z hz
    have := hvan t ht
    simpa using this
  obtain ⟨r, Q, hQ0, hQ⟩ := exists_uniform_jet_relation_of_linearized_tower hUo hUc hUne hUinf
    hVo hVc hVne hVinf hΦ hg hmaps' hfaith' hΦDA hgDA
  refine differentiallyAlgebraicOn_of_eqOn hUo (fun t _ => ?_)
    (differentiallyAlgebraicOn_of_autonomous_relation (h := fun s => Φ ((1 : ℂ) ^ 0 * g s))
      hQ0 (hQ 0))
  simp

/-- **Equation (9).**  The tower of a conjugated germ is the conjugated tower. -/
theorem iterate_conjugate {W W' : Set ℂ} {f hh hhInv : ℂ → ℂ}
    (hInvMaps : Set.MapsTo hhInv W W') (hfMaps : Set.MapsTo f W' W')
    (hMaps : Set.MapsTo hh W' W) (hleft : ∀ t ∈ W, hh (hhInv t) = t)
    (hright : ∀ z ∈ W', hhInv (hh z) = z) :
    ∀ (n : ℕ), ∀ t ∈ W, (fun s => hh (f (hhInv s)))^[n] t = hh (f^[n] (hhInv t)) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      simpa using (hleft t ht).symm
  | succ n ih =>
      intro t ht
      have hmem : hh (f (hhInv t)) ∈ W := hMaps (hfMaps (hInvMaps ht))
      rw [Function.iterate_succ_apply]
      have hstep : (fun s => hh (f (hhInv s)))^[n] (hh (f (hhInv t)))
          = hh (f^[n] (hhInv (hh (f (hhInv t))))) := ih _ hmem
      rw [hstep, hright _ (hfMaps (hInvMaps ht)), ← Function.iterate_succ_apply]

/-- **DA-scheme invariance `(10)`.**  Reading the linearizing coordinate through a locally
invertible differentially algebraic scheme neither creates nor destroys differential algebraicity,
so the coherence obstruction is a property of the germ and not of the chart. -/
theorem differentiallyAlgebraicOn_comp_iff_of_scheme
    {U U' : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) (hU'o : IsOpen U') (hU'c : IsPreconnected U') (hU'ne : U'.Nonempty)
    (hU'inf : U'.Infinite) {κ hh hhInv : ℂ → ℂ} (hκ : AnalyticOnNhd ℂ κ U)
    (hhh : AnalyticOnNhd ℂ hh U) (hhhInv : AnalyticOnNhd ℂ hhInv U')
    (hInvMaps : Set.MapsTo hhInv U' U) (hMaps : Set.MapsTo hh U U')
    (hleft : ∀ t ∈ U', hh (hhInv t) = t) (hright : ∀ t ∈ U, hhInv (hh t) = t)
    (hfaithInv : SubstitutionFaithful U' U hhInv)
    (hhhDA : DifferentiallyAlgebraicOn hh U) (hκDA : DifferentiallyAlgebraicOn κ U) :
    DifferentiallyAlgebraicOn (fun t => κ (hhInv t)) U' := by
  have hhhInvDA : DifferentiallyAlgebraicOn hhInv U' :=
    differentiallyAlgebraicOn_of_localInverse hUo hUc hUne hUinf hhhInv hhh hMaps hInvMaps
      hright hleft hhhDA
  exact differentiallyAlgebraicOn_comp hU'o hU'c hU'ne hU'inf hUo hUc hUne hUinf
    hκ hhhInv hInvMaps hfaithInv hκDA hhhInvDA

/-! ## The hypotheses are satisfiable -/

/-- The scaled coordinate maps the linearizing domain into itself at every stage. -/
theorem mapsTo_pow_smul {V : Set ℂ} {lam : ℂ} (hscale : Set.MapsTo (fun z => lam * z) V V) :
    ∀ n : ℕ, Set.MapsTo (fun z => lam ^ n * z) V V := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simpa using hz
  | succ n ih =>
      intro z hz
      have h : lam * (lam ^ n * z) ∈ V := hscale (ih hz)
      show lam ^ (n + 1) * z ∈ V
      rwa [show lam ^ (n + 1) * z = lam * (lam ^ n * z) from by ring]

/-- **The substitutions of a linearized tower are faithful.**  Each scaled coordinate hits the
open set `λ^n · V`, on which the linearizing coordinate provides a right inverse. -/
theorem substitutionFaithful_scaled_linearizer {U V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hVne : V.Nonempty) {Φ κ : ℂ → ℂ} (hΦU : Set.MapsTo Φ V U)
    (hκΦ : ∀ z ∈ V, κ (Φ z) = z) {lam : ℂ} (hlam : lam ≠ 0)
    (hscale : Set.MapsTo (fun z => lam * z) V V) (n : ℕ) :
    SubstitutionFaithful U V (fun t => lam ^ n * κ t) := by
  have hlamn : lam ^ n ≠ 0 := pow_ne_zero n hlam
  set W : Set ℂ := {w : ℂ | w / lam ^ n ∈ V} with hW
  have hWo : IsOpen W := by
    have hcont : Continuous fun w : ℂ => w / lam ^ n := continuous_id.div_const _
    exact hVo.preimage hcont
  have hWne : W.Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨lam ^ n * v, ?_⟩
    show lam ^ n * v / lam ^ n ∈ V
    rwa [mul_comm, mul_div_assoc, div_self hlamn, mul_one]
  have hWV : W ⊆ V := by
    intro w hw
    have h : lam ^ n * (w / lam ^ n) ∈ V := mapsTo_pow_smul hscale n hw
    have hval : lam ^ n * (w / lam ^ n) = w := by
      field_simp
    rwa [hval] at h
  refine substitutionFaithful_of_rightInverse hVc hWo hWne hWV
    (ρ := fun w => Φ (w / lam ^ n)) (fun w hw => hΦU hw) (fun w hw => ?_)
  show lam ^ n * κ (Φ (w / lam ^ n)) = w
  rw [hκΦ _ hw]
  field_simp

end

end GaloisForLFunctions.HTGeometry
