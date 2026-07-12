import GaloisForLFunctions.DifferentialUnitEquation

/-!
# The differentiation-elimination engine

The `𝒟`-on-coefficients analog of `gammaPowerRel_eq_zero` — the elimination that turns a
power relation of a logarithmic-derivative object into a differential-algebraic relation for
the log-derivative itself.

Let `f, u : ℂ → ℂ` with `f' = u·f` and `f ≠ 0` on an open set `Ω`, and let
`J z = (z, u(z), u'(z), …)` be the jet vector (`J z 0 = z`, `J z (k+1) = u⁽ᵏ⁾(z)`).  A
**power relation** is `∑_{d≤D} f(z)^d · (J z)(Q_d) = 0` on `Ω`, with coefficients
`Q_d ∈ MvPolynomial ℕ ℂ` in the jet variables `x₀ = s`, `x₁ = u`, `x_{j+1} = u⁽ʲ⁾`.

**`diffPowerRel_yields`** — if such a relation holds with not all `Q_d` zero, then there is a
nonzero `R ∈ MvPolynomial ℕ ℂ` whose jet evaluation vanishes on `Ω`: a differential-algebraic
relation for `u`.  The proof is the differential twin of `gammaPowerRel_eq_zero`:
differentiating the relation replaces the coefficient `Q_d` by `L d Q_d = 𝒟 Q_d + d·x₁·Q_d`
(`derivedRelation`, the analytic step); combining with the top coefficient eliminates the
top power (`elimRelation`); strong induction on the degree either bottoms out at a single
surviving term — whose vanishing (`f ≠ 0`) is the `u`-relation — or reaches the differential
eigenrelation, refuted by `no_differential_eigenrelation`.

Unlike the Γ-transfer's shift elimination there is no denominator clearing: with `s = x₀` a
jet variable the coefficients are already in `MvPolynomial ℕ ℂ`, and `totalDeriv` is exactly
the total derivative used by the no-go.  The analytic content — that `f' = u·f`, that the jet
evaluation differentiates by `𝒟`, and that `f ≠ 0` — enters only as the `HasDerivAt`
hypotheses `hf`, `hJ`, `hfne`.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial Filter Topology

/-! ## The analytic step: differentiating the relation -/

/-- Product rule for a single power-relation term: `(f^d·(J·)Q)' = f^d·(J·)(𝒟Q + d·x₁·Q)`. -/
theorem hasDerivAt_powerTerm {f : ℂ → ℂ} {J : ℂ → ℕ → ℂ} {z : ℂ}
    (hf : HasDerivAt f (eval (J z) (X 1) * f z) z)
    (hJ : ∀ P : MvPolynomial ℕ ℂ,
      HasDerivAt (fun w => eval (J w) P) (eval (J z) (totalDeriv P)) z)
    (d : ℕ) (Q : MvPolynomial ℕ ℂ) :
    HasDerivAt (fun w => f w ^ d * eval (J w) Q)
      (f z ^ d * eval (J z) (totalDeriv Q + C (d : ℂ) * X 1 * Q)) z := by
  have hprod := (hf.pow d).mul (hJ Q)
  convert hprod using 1
  simp only [Pi.pow_apply]
  rw [map_add, map_mul, map_mul, eval_C, eval_X]
  cases d with
  | zero => simp
  | succ k => rw [pow_succ]; push_cast; ring

/-- The `L`-operator on coefficients: `L d Q = 𝒟 Q + d·x₁·Q`. -/
def Lop (d : ℕ) (Q : MvPolynomial ℕ ℂ) : MvPolynomial ℕ ℂ :=
  totalDeriv Q + C (d : ℂ) * X 1 * Q

/-- **The derived relation.**  Differentiating a power relation on the open set replaces each
coefficient `Q_d` by `L d Q_d`. -/
theorem derivedRelation {f : ℂ → ℂ} {J : ℂ → ℕ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ z ∈ Ω, HasDerivAt f (eval (J z) (X 1) * f z) z)
    (hJ : ∀ (P : MvPolynomial ℕ ℂ), ∀ z ∈ Ω,
      HasDerivAt (fun w => eval (J w) P) (eval (J z) (totalDeriv P)) z)
    {D : ℕ} {Q : ℕ → MvPolynomial ℕ ℂ}
    (hrel : ∀ z ∈ Ω, ∑ d ∈ Finset.range (D + 1), f z ^ d * eval (J z) (Q d) = 0)
    (z : ℂ) (hz : z ∈ Ω) :
    ∑ d ∈ Finset.range (D + 1), f z ^ d * eval (J z) (Lop d (Q d)) = 0 := by
  set g : ℂ → ℂ := fun w => ∑ d ∈ Finset.range (D + 1), f w ^ d * eval (J w) (Q d) with hg
  have hgderiv : HasDerivAt g
      (∑ d ∈ Finset.range (D + 1), f z ^ d * eval (J z) (Lop d (Q d))) z := by
    apply HasDerivAt.fun_sum
    intro d _
    exact hasDerivAt_powerTerm (hf z hz) (fun P => hJ P z hz) d (Q d)
  have hgzero : g =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hΩ.mem_nhds hz] with w hw
    exact hrel w hw
  have hg0 : HasDerivAt g 0 z :=
    (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq hgzero
  exact hgderiv.unique hg0

/-! ## The elimination step -/

/-- Eliminated coefficients: `T d = Q_{D'}·L d (Q d) − L D' (Q_{D'})·Q d`. -/
def Telim (D' : ℕ) (Q : ℕ → MvPolynomial ℕ ℂ) (d : ℕ) : MvPolynomial ℕ ℂ :=
  Q D' * Lop d (Q d) - Lop D' (Q D') * Q d

theorem Telim_top (D' : ℕ) (Q : ℕ → MvPolynomial ℕ ℂ) : Telim D' Q D' = 0 := by
  unfold Telim; ring

/-- **The eliminated relation.**  Combining the original and derived relations against the
top coefficient kills the top power. -/
theorem elimRelation {f : ℂ → ℂ} {J : ℂ → ℕ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ z ∈ Ω, HasDerivAt f (eval (J z) (X 1) * f z) z)
    (hJ : ∀ (P : MvPolynomial ℕ ℂ), ∀ z ∈ Ω,
      HasDerivAt (fun w => eval (J w) P) (eval (J z) (totalDeriv P)) z)
    {D' : ℕ} {Q : ℕ → MvPolynomial ℕ ℂ}
    (hrel : ∀ z ∈ Ω, ∑ d ∈ Finset.range (D' + 1), f z ^ d * eval (J z) (Q d) = 0)
    (z : ℂ) (hz : z ∈ Ω) :
    ∑ d ∈ Finset.range (D' + 1), f z ^ d * eval (J z) (Telim D' Q d) = 0 := by
  have hderiv := derivedRelation hΩ hf hJ hrel z hz
  have horig := hrel z hz
  have hkey : ∑ d ∈ Finset.range (D' + 1), f z ^ d * eval (J z) (Telim D' Q d)
      = eval (J z) (Q D')
          * ∑ d ∈ Finset.range (D' + 1), f z ^ d * eval (J z) (Lop d (Q d))
        - eval (J z) (Lop D' (Q D'))
          * ∑ d ∈ Finset.range (D' + 1), f z ^ d * eval (J z) (Q d) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Telim, map_sub, map_mul, map_mul]
    ring
  rw [hkey, hderiv, horig, mul_zero, mul_zero, sub_zero]

/-! ## The elimination engine -/

/-- **The differentiation-elimination engine.**  A power relation `∑_{d≤D} f^d·(J·)Q_d = 0`
on the open set `Ω` (with `f' = u·f`, `f ≠ 0`, the jet evaluation differentiating by `𝒟`)
whose coefficients are not all zero yields a nonzero differential-algebraic relation for the
jet vector `u`: a nonzero `R` with `(J z)(R) = 0` on `Ω`. -/
theorem diffPowerRel_yields {f : ℂ → ℂ} {J : ℂ → ℕ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ z ∈ Ω, HasDerivAt f (eval (J z) (X 1) * f z) z)
    (hJ : ∀ (P : MvPolynomial ℕ ℂ), ∀ z ∈ Ω,
      HasDerivAt (fun w => eval (J w) P) (eval (J z) (totalDeriv P)) z)
    (hfne : ∀ z ∈ Ω, f z ≠ 0) :
    ∀ (D : ℕ) (Q : ℕ → MvPolynomial ℕ ℂ),
      (∀ z ∈ Ω, ∑ d ∈ Finset.range (D + 1), f z ^ d * eval (J z) (Q d) = 0) →
      (∃ d ∈ Finset.range (D + 1), Q d ≠ 0) →
      ∃ R : MvPolynomial ℕ ℂ, R ≠ 0 ∧ ∀ z ∈ Ω, eval (J z) R = 0 := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro Q hrel hne
    by_cases hQD : Q D = 0
    · cases D with
      | zero =>
        obtain ⟨d, hd, hdne⟩ := hne
        rw [Finset.mem_range, Nat.lt_one_iff] at hd
        subst hd; exact absurd hQD hdne
      | succ D0 =>
        have hrel' : ∀ z ∈ Ω,
            ∑ d ∈ Finset.range (D0 + 1), f z ^ d * eval (J z) (Q d) = 0 := by
          intro z hz
          have h := hrel z hz
          rw [Finset.sum_range_succ, hQD, map_zero, mul_zero, add_zero] at h
          exact h
        have hne' : ∃ d ∈ Finset.range (D0 + 1), Q d ≠ 0 := by
          obtain ⟨d, hd, hdne⟩ := hne
          rw [Finset.mem_range] at hd
          refine ⟨d, Finset.mem_range.mpr ?_, hdne⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hd with h | h
          · exact h
          · subst h; exact absurd hQD hdne
        exact ih D0 (by omega) Q hrel' hne'
    · by_cases hlow : ∃ d ∈ Finset.range D, Q d ≠ 0
      · by_cases hTzero : ∀ d ∈ Finset.range D, Telim D Q d = 0
        · obtain ⟨d0, hd0mem, hd0ne⟩ := hlow
          rw [Finset.mem_range] at hd0mem
          have hTd0 := hTzero d0 (Finset.mem_range.mpr hd0mem)
          exfalso
          apply no_differential_eigenrelation hd0ne hQD (by omega : 1 ≤ D - d0)
          have hcast : ((D - d0 : ℕ) : ℂ) = (D : ℂ) - (d0 : ℂ) :=
            Nat.cast_sub (le_of_lt hd0mem)
          unfold Telim Lop at hTd0
          rw [hcast, map_sub]
          linear_combination hTd0
        · simp only [not_forall] at hTzero
          obtain ⟨d1, hd1⟩ := hTzero
          have hDe : D - 1 + 1 = D := by
            obtain ⟨d, hd, _⟩ := hlow; rw [Finset.mem_range] at hd; omega
          have hTrel : ∀ z ∈ Ω,
              ∑ d ∈ Finset.range (D - 1 + 1), f z ^ d * eval (J z) (Telim D Q d) = 0 := by
            intro z hz
            rw [hDe]
            have h := elimRelation hΩ hf hJ hrel z hz
            rw [Finset.sum_range_succ, Telim_top, map_zero, mul_zero, add_zero] at h
            exact h
          have hTne : ∃ d ∈ Finset.range (D - 1 + 1), Telim D Q d ≠ 0 := by
            obtain ⟨hd1mem, hd1ne⟩ := hd1
            refine ⟨d1, ?_, hd1ne⟩
            rw [Finset.mem_range] at hd1mem ⊢; omega
          exact ih (D - 1) (by omega) (Telim D Q) hTrel hTne
      · simp only [not_exists, not_and, not_not] at hlow
        refine ⟨Q D, hQD, fun z hz => ?_⟩
        have h := hrel z hz
        rw [Finset.sum_range_succ,
          Finset.sum_eq_zero (fun d hd => by
            rw [Finset.mem_range] at hd
            rw [hlow d (Finset.mem_range.mpr hd), map_zero, mul_zero]),
          zero_add] at h
        exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hfne z hz))

/-! ## The concrete jet vector and its chain rule -/

/-- The jet vector of `u`: `uJet u z 0 = z`, `uJet u z (k+1) = u⁽ᵏ⁾(z)`. -/
def uJet (u : ℂ → ℂ) (z : ℂ) : ℕ → ℂ :=
  fun n => if n = 0 then z else iteratedDeriv (n - 1) u z

theorem uJet_one (u : ℂ → ℂ) (z : ℂ) : uJet u z 1 = u z := by
  simp [uJet, iteratedDeriv_zero]

/-- Each iterated derivative of an analytic function differentiates to the next. -/
theorem hasDerivAt_iteratedDeriv_of_analyticOn {u : ℂ → ℂ} {Ω : Set ℂ}
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z) (k : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    HasDerivAt (iteratedDeriv k u) (iteratedDeriv (k + 1) u z) z := by
  have han : AnalyticAt ℂ (iteratedDeriv k u) z := by
    have hanu : AnalyticOnNhd ℂ u Ω := fun w hw => hu w hw
    have hall : AnalyticOnNhd ℂ (iteratedDeriv k u) Ω := by
      clear hz
      induction k with
      | zero => simpa [iteratedDeriv_zero] using hanu
      | succ k ih =>
          intro w hw
          rw [iteratedDeriv_succ]
          exact (ih w hw).deriv
    exact hall z hz
  have hda := han.differentiableAt.hasDerivAt
  rw [iteratedDeriv_succ]
  exact hda

/-- The jet component `w ↦ uJet u w i` differentiates to `(J·)(totalDerivGen i)`. -/
theorem hasDerivAt_uJet_component {u : ℂ → ℂ} {Ω : Set ℂ}
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z) (i : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    HasDerivAt (fun w => uJet u w i) (eval (uJet u z) (totalDerivGen i)) z := by
  cases i with
  | zero =>
      simp only [uJet, if_pos, totalDerivGen_zero, map_one]
      exact hasDerivAt_id z
  | succ k =>
      have hcomp : (fun w => uJet u w (k + 1)) = iteratedDeriv k u := by
        funext w; simp [uJet]
      rw [hcomp, totalDerivGen_succ, eval_X]
      have hval : uJet u z (k + 2) = iteratedDeriv (k + 1) u z := by simp [uJet]
      rw [hval]
      exact hasDerivAt_iteratedDeriv_of_analyticOn hu k hz

/-- **The chain rule for jet evaluation.**  For `u` analytic on `Ω`, the map
`w ↦ (uJet u w)(P)` differentiates to `(uJet u z)(𝒟 P)` — the `hJ` hypothesis of the engine. -/
theorem hasDerivAt_uJetEval {u : ℂ → ℂ} {Ω : Set ℂ}
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z) (P : MvPolynomial ℕ ℂ) {z : ℂ} (hz : z ∈ Ω) :
    HasDerivAt (fun w => eval (uJet u w) P) (eval (uJet u z) (totalDeriv P)) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [eval_C, totalDeriv_C, map_zero]
      exact hasDerivAt_const z a
  | add P Q hP hQ =>
      simp only [map_add]
      exact hP.add hQ
  | mul_X P i hP =>
      have hfun : (fun w => eval (uJet u w) (P * X i))
          = fun w => eval (uJet u w) P * uJet u w i := by
        funext w; rw [map_mul, eval_X]
      rw [hfun]
      have hd := hP.mul (hasDerivAt_uJet_component hu i hz)
      convert hd using 1
      rw [Derivation.leibniz, totalDeriv_X, smul_eq_mul, smul_eq_mul, map_add,
        map_mul, map_mul, eval_X]
      ring

/-! ## The packaged capstone -/

/-- **Log-derivative differential algebraicity from a power relation.**  For `f` analytic
and nonzero on the open set `Ω`, a nonzero power relation `∑ f^d·(uJet u·)Q_d = 0`
(`u = f'/f`) yields a nonzero differential-algebraic relation for `u = f'/f` on `Ω`. -/
theorem logDeriv_DA_of_powerRel {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hfan : ∀ z ∈ Ω, AnalyticAt ℂ f z) (hfne : ∀ z ∈ Ω, f z ≠ 0)
    {D : ℕ} {Q : ℕ → MvPolynomial ℕ ℂ}
    (hrel : ∀ z ∈ Ω, ∑ d ∈ Finset.range (D + 1),
      f z ^ d * eval (uJet (fun w => deriv f w / f w) z) (Q d) = 0)
    (hne : ∃ d ∈ Finset.range (D + 1), Q d ≠ 0) :
    ∃ R : MvPolynomial ℕ ℂ, R ≠ 0 ∧
      ∀ z ∈ Ω, eval (uJet (fun w => deriv f w / f w) z) R = 0 := by
  set u : ℂ → ℂ := fun w => deriv f w / f w with hu_def
  have huan : ∀ z ∈ Ω, AnalyticAt ℂ u z :=
    fun z hz => (hfan z hz).deriv.div (hfan z hz) (hfne z hz)
  have hf : ∀ z ∈ Ω, HasDerivAt f (eval (uJet u z) (X 1) * f z) z := by
    intro z hz
    rw [eval_X]
    have hval : uJet u z 1 * f z = deriv f z := by
      rw [uJet_one]
      exact div_mul_cancel₀ (deriv f z) (hfne z hz)
    rw [hval]
    exact (hfan z hz).differentiableAt.hasDerivAt
  have hJ : ∀ (P : MvPolynomial ℕ ℂ), ∀ z ∈ Ω,
      HasDerivAt (fun w => eval (uJet u w) P) (eval (uJet u z) (totalDeriv P)) z :=
    fun P z hz => hasDerivAt_uJetEval huan P hz
  exact diffPowerRel_yields hΩ hf hJ hfne D Q hrel hne

end GaloisForLFunctions

end
